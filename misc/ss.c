/*
 * ss.c		"sockstat", socket statistics
 *
 *		This program is free software; you can redistribute it and/or
 *		modify it under the terms of the GNU General Public License
 *		as published by the Free Software Foundation; either version
 *		2 of the License, or (at your option) any later version.
 *
 * Authors:	Alexey Kuznetsov, <kuznet@ms2.inr.ac.ru>
 */

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/ioctl.h>
#include <sys/socket.h>
#include <sys/uio.h>
#include <sys/sysmacros.h>
#include <netinet/in.h>
#include <string.h>
#include <errno.h>
#include <netdb.h>
#include <arpa/inet.h>
#include <dirent.h>
#include <fnmatch.h>
#include <getopt.h>
#include <stdbool.h>
#include <limits.h>
#include <stdarg.h>

#include "utils.h"
#include "rt_names.h"
#include "ll_map.h"
#include "libnetlink.h"
#include "namespace.h"
#include "SNAPSHOT.h"

#include <linux/tcp.h>
#include <linux/sock_diag.h>
#include <linux/inet_diag.h>
#include <linux/unix_diag.h>
#include <linux/netdevice.h>	/* for MAX_ADDR_LEN */
#include <linux/filter.h>
#include <linux/xdp_diag.h>
#include <linux/packet_diag.h>
#include <linux/netlink_diag.h>
#include <linux/sctp.h>
#include <linux/vm_sockets_diag.h>
#include <linux/net.h>
#include <linux/tipc.h>
#include <linux/tipc_netlink.h>
#include <linux/tipc_sockets_diag.h>

/* AF_VSOCK/PF_VSOCK is only provided since glibc 2.18 */
#ifndef PF_VSOCK
#define PF_VSOCK 40
#endif
#ifndef AF_VSOCK
#define AF_VSOCK PF_VSOCK
#endif

#define MAGIC_SEQ 123456
#define LEN_ALIGN(x) (((x) + 1) & ~1)

#define DIAG_REQUEST(_req, _r)						    \
	struct {							    \
		struct nlmsghdr nlh;					    \
		_r;							    \
	} _req = {							    \
		.nlh = {						    \
			.nlmsg_type = SOCK_DIAG_BY_FAMILY,		    \
			.nlmsg_flags = NLM_F_ROOT|NLM_F_MATCH|NLM_F_REQUEST,\
			.nlmsg_seq = MAGIC_SEQ,				    \
			.nlmsg_len = sizeof(_req),			    \
		},							    \
	}

#if HAVE_SELINUX
#include <selinux/selinux.h>
#else

static int getpidcon(pid_t pid, char **context)
{
	*context = NULL;
	return -1;
}

static int getfilecon(char *path, char **context)
{
	*context = NULL;
	return -1;
}

#endif

int preferred_family = AF_UNSPEC;
static int show_options;
int show_details;
static int show_users = 1;
static int show_mem = 1;
static int show_tcpinfo = 1;
static int show_proc_ctx = 0;
static int show_sock_ctx = 0;
static int sctp_ino;
static int show_tos;

enum {
	SS_UNKNOWN,
	SS_ESTABLISHED,
	SS_SYN_SENT,
	SS_SYN_RECV,
	SS_FIN_WAIT1,
	SS_FIN_WAIT2,
	SS_TIME_WAIT,
	SS_CLOSE,
	SS_CLOSE_WAIT,
	SS_LAST_ACK,
	SS_LISTEN,
	SS_CLOSING,
	SS_MAX
};

#define SS_ALL ((1 << SS_MAX) - 1)
#define SS_CONN (SS_ALL & ~((1<<SS_LISTEN)|(1<<SS_CLOSE)|(1<<SS_TIME_WAIT)|(1<<SS_SYN_RECV)))

#include "ssfilter.h"

struct filter {
	int states;
	uint64_t families;
	struct ssfilter *f;
	bool kill;
	struct rtnl_handle *rth_for_killing;
};

#define FAMILY_MASK(family) ((uint64_t)1 << (family))

static struct filter current_filter;

static FILE *generic_proc_open(const char *env, const char *name)
{
	const char *p = getenv(env);
	char store[128];

	if (!p) {
		p = getenv("PROC_ROOT") ? : "/proc";
		snprintf(store, sizeof(store)-1, "%s/%s", p, name);
		p = store;
	}

	return fopen(p, "r");
}
#define net_tcp_open()		generic_proc_open("PROC_NET_TCP", "net/tcp")
#define net_tcp6_open()		generic_proc_open("PROC_NET_TCP6", "net/tcp6")
#define net_udp_open()		generic_proc_open("PROC_NET_UDP", "net/udp")
#define net_udp6_open()		generic_proc_open("PROC_NET_UDP6", "net/udp6")
#define net_raw_open()		generic_proc_open("PROC_NET_RAW", "net/raw")
#define net_raw6_open()		generic_proc_open("PROC_NET_RAW6", "net/raw6")
#define net_unix_open()		generic_proc_open("PROC_NET_UNIX", "net/unix")
#define net_packet_open()	generic_proc_open("PROC_NET_PACKET", \
							"net/packet")
#define net_netlink_open()	generic_proc_open("PROC_NET_NETLINK", \
							"net/netlink")
#define net_sockstat_open()	generic_proc_open("PROC_NET_SOCKSTAT", \
							"net/sockstat")
#define net_sockstat6_open()	generic_proc_open("PROC_NET_SOCKSTAT6", \
							"net/sockstat6")
#define net_snmp_open()		generic_proc_open("PROC_NET_SNMP", "net/snmp")
#define ephemeral_ports_open()	generic_proc_open("PROC_IP_LOCAL_PORT_RANGE", \
					"sys/net/ipv4/ip_local_port_range")

struct user_ent {
	struct user_ent	*next;
	unsigned int	ino;
	int		pid;
	int		fd;
	char		*process;
	char		*process_ctx;
	char		*socket_ctx;
};

#define USER_ENT_HASH_SIZE	256
static struct user_ent *user_ent_hash[USER_ENT_HASH_SIZE];

static int user_ent_hashfn(unsigned int ino)
{
	int val = (ino >> 24) ^ (ino >> 16) ^ (ino >> 8) ^ ino;

	return val & (USER_ENT_HASH_SIZE - 1);
}

static void user_ent_add(unsigned int ino, char *process,
					int pid, int fd,
					char *proc_ctx,
					char *sock_ctx)
{
	struct user_ent *p, **pp;

	p = malloc(sizeof(struct user_ent));
	if (!p) {
		fprintf(stderr, "ss: failed to malloc buffer\n");
		abort();
	}
	p->next = NULL;
	p->ino = ino;
	p->pid = pid;
	p->fd = fd;
	p->process = strdup(process);
	p->process_ctx = strdup(proc_ctx);
	p->socket_ctx = strdup(sock_ctx);

	pp = &user_ent_hash[user_ent_hashfn(ino)];
	p->next = *pp;
	*pp = p;
}

static void user_ent_destroy(void)
{
	struct user_ent *p, *p_next;
	int cnt = 0;

	while (cnt != USER_ENT_HASH_SIZE) {
		p = user_ent_hash[cnt];
		while (p) {
			free(p->process);
			free(p->process_ctx);
			free(p->socket_ctx);
			p_next = p->next;
			free(p);
			p = p_next;
		}
		cnt++;
	}
}

static void user_ent_hash_build(void)
{
	const char *root = getenv("PROC_ROOT") ? : "/proc/";
	struct dirent *d;
	char name[1024];
	int nameoff;
	DIR *dir;
	char *pid_context;
	char *sock_context;
	const char *no_ctx = "unavailable";
	static int user_ent_hash_build_init;

	/* If show_users & show_proc_ctx set only do this once */
	if (user_ent_hash_build_init != 0)
		return;

	user_ent_hash_build_init = 1;

	strlcpy(name, root, sizeof(name));

	if (strlen(name) == 0 || name[strlen(name)-1] != '/')
		strcat(name, "/");

	nameoff = strlen(name);

	dir = opendir(name);
	if (!dir)
		return;

	while ((d = readdir(dir)) != NULL) {
		struct dirent *d1;
		char process[16];
		char *p;
		int pid, pos;
		DIR *dir1;
		char crap;

		if (sscanf(d->d_name, "%d%c", &pid, &crap) != 1)
			continue;

		if (getpidcon(pid, &pid_context) != 0)
			pid_context = strdup(no_ctx);

		snprintf(name + nameoff, sizeof(name) - nameoff, "%d/fd/", pid);
		pos = strlen(name);
		if ((dir1 = opendir(name)) == NULL) {
			free(pid_context);
			continue;
		}

		process[0] = '\0';
		p = process;

		while ((d1 = readdir(dir1)) != NULL) {
			const char *pattern = "socket:[";
			unsigned int ino;
			char lnk[64];
			int fd;
			ssize_t link_len;
			char tmp[1024];

			if (sscanf(d1->d_name, "%d%c", &fd, &crap) != 1)
				continue;

			snprintf(name+pos, sizeof(name) - pos, "%d", fd);

			link_len = readlink(name, lnk, sizeof(lnk)-1);
			if (link_len == -1)
				continue;
			lnk[link_len] = '\0';

			if (strncmp(lnk, pattern, strlen(pattern)))
				continue;

			sscanf(lnk, "socket:[%u]", &ino);

			snprintf(tmp, sizeof(tmp), "%s/%d/fd/%s",
					root, pid, d1->d_name);

			if (getfilecon(tmp, &sock_context) <= 0)
				sock_context = strdup(no_ctx);

			if (*p == '\0') {
				FILE *fp;

				snprintf(tmp, sizeof(tmp), "%s/%d/stat",
					root, pid);
				if ((fp = fopen(tmp, "r")) != NULL) {
					if (fscanf(fp, "%*d (%[^)])", p) < 1)
						; /* ignore */
					fclose(fp);
				}
			}
			user_ent_add(ino, p, pid, fd,
					pid_context, sock_context);
			free(sock_context);
		}
		free(pid_context);
		closedir(dir1);
	}
	closedir(dir);
}

enum entry_types {
	USERS,
	PROC_CTX,
	PROC_SOCK_CTX
};

#define ENTRY_BUF_SIZE 512
static int find_entry(unsigned int ino, int type)
{
	struct user_ent *p;
	int cnt = 0;

	if (!ino)
		return 0;

	p = user_ent_hash[user_ent_hashfn(ino)];
	while (p) {
		if (p->ino != ino)
			goto next;

        switch (type) {
        case USERS:
            printf("{\"name\": \"%s\", \"pid\": %d, \"fd\": %d},",
                p->process, p->pid, p->fd);
            break;
        case PROC_CTX:
            printf("{\"name\": \"%s\", \"pid\": %d, \"proc_ctx\": \"%s\", \"fd\": %d},",
                p->process, p->pid,
                p->process_ctx, p->fd);
            break;
        case PROC_SOCK_CTX:
            printf("{\"name\": \"%s\", \"pid\": %d, \"proc_ctx\": \"%s\", \"fd\": %d, \"sock_ctx\": \"%s\"},",
                p->process, p->pid,
                p->process_ctx, p->fd,
                p->socket_ctx);
            break;
        default:
            fprintf(stderr, "ss: invalid type: %d\n", type);
            abort();
        }
		cnt++;
next:
		p = p->next;
	}
	return cnt;
}

static unsigned long long cookie_sk_get(const uint32_t *cookie)
{
	return (((unsigned long long)cookie[1] << 31) << 1) | cookie[0];
}

struct sockstat {
	struct sockstat	   *next;
	unsigned int	    type;
	uint16_t	    prot;
	uint16_t	    raw_prot;
	inet_prefix	    local;
	inet_prefix	    remote;
	int		    lport;
	int		    rport;
	int		    state;
	int		    rq, wq;
	unsigned int ino;
	unsigned int uid;
	int		    refcnt;
	unsigned int	    iface;
	unsigned long long  sk;
	char *name;
	char *peer_name;
	__u32		    mark;
};

struct dctcpstat {
	unsigned int	ce_state;
	unsigned int	alpha;
	unsigned int	ab_ecn;
	unsigned int	ab_tot;
	bool		enabled;
};

struct tcpstat {
	struct sockstat	    ss;
	unsigned int	    timer;
	unsigned int	    timeout;
	int		    probes;
	char		    cong_alg[16];
	double		    rto, ato, rtt, rttvar;
	int		    qack, ssthresh, backoff;
	double		    send_bps;
	int		    snd_wscale;
	int		    rcv_wscale;
	int		    mss;
	int		    rcv_mss;
	int		    advmss;
	unsigned int	    pmtu;
	unsigned int	    cwnd;
	unsigned int	    lastsnd;
	unsigned int	    lastrcv;
	unsigned int	    lastack;
	double		    pacing_rate;
	double		    pacing_rate_max;
	double		    delivery_rate;
	unsigned long long  bytes_acked;
	unsigned long long  bytes_received;
	unsigned int	    segs_out;
	unsigned int	    segs_in;
	unsigned int	    data_segs_out;
	unsigned int	    data_segs_in;
	unsigned int	    unacked;
	unsigned int	    retrans;
	unsigned int	    retrans_total;
	unsigned int	    lost;
	unsigned int	    sacked;
	unsigned int	    fackets;
	unsigned int	    reordering;
	unsigned int	    not_sent;
	unsigned int	    delivered;
	unsigned int	    delivered_ce;
	unsigned int	    dsack_dups;
	unsigned int	    reord_seen;
	double		    rcv_rtt;
	double		    min_rtt;
	int		    rcv_space;
	unsigned int        rcv_ssthresh;
	unsigned long long  busy_time;
	unsigned long long  rwnd_limited;
	unsigned long long  sndbuf_limited;
	unsigned long long  bytes_sent;
	unsigned long long  bytes_retrans;
	bool		    has_ts_opt;
	bool		    has_sack_opt;
	bool		    has_ecn_opt;
	bool		    has_ecnseen_opt;
	bool		    has_fastopen_opt;
	bool		    has_wscale_opt;
	bool		    app_limited;
	struct dctcpstat    *dctcp;
	struct tcp_bbr_info *bbr_info;
};

/* SCTP assocs share the same inode number with their parent endpoint. So if we
 * have seen the inode number before, it must be an assoc instead of the next
 * endpoint. */
static void sock_state_print(struct sockstat *s)
{
	static const char * const sstate_name[] = {
		"UNKNOWN",
		[SS_ESTABLISHED] = "ESTAB",
		[SS_SYN_SENT] = "SYN-SENT",
		[SS_SYN_RECV] = "SYN-RECV",
		[SS_FIN_WAIT1] = "FIN-WAIT-1",
		[SS_FIN_WAIT2] = "FIN-WAIT-2",
		[SS_TIME_WAIT] = "TIME-WAIT",
		[SS_CLOSE] = "UNCONN",
		[SS_CLOSE_WAIT] = "CLOSE-WAIT",
		[SS_LAST_ACK] = "LAST-ACK",
		[SS_LISTEN] =	"LISTEN",
		[SS_CLOSING] = "CLOSING",
	};

    printf("\"state\": \"%s\", ", sstate_name[s->state]);

	printf("\"recvq\": %d, ", s->rq);
	printf("\"sendq\": %d, ", s->wq);
}

static void sock_details_print(struct sockstat *s)
{
	if (s->uid)
		printf("\"uid\": %u, ", s->uid);

	printf("\"ino\": %u, ", s->ino);
	printf("\"sk\": %llu, ", s->sk);

	if (s->mark)
		printf(" fwmark:0x%x", s->mark);
}

static void sock_addr_print(const char *addr, char *delim, const int port,
		const char *ifname)
{
	if (ifname)
		printf("\"addr\": \"%s\", \"interface\": \"%s\", ", addr, ifname);
	else
		printf("\"addr\": \"%s\", ", addr);

	printf("\"port\": \"%d\"", port);
}

struct scache {
	struct scache *next;
	int port;
	char *name;
	const char *proto;
};

/* Even do not try default linux ephemeral port ranges:
 * default /etc/services contains so much of useless crap
 * wouldbe "allocated" to this area that resolution
 * is really harmful. I shrug each time when seeing
 * "socks" or "cfinger" in dumps.
 */
static int is_ephemeral(int port)
{
	static int min = 0, max;

	if (!min) {
		FILE *f = ephemeral_ports_open();

		if (!f || fscanf(f, "%d %d", &min, &max) < 2) {
			min = 1024;
			max = 4999;
		}
		if (f)
			fclose(f);
	}
	return port >= min && port <= max;
}


static void inet_addr_print(const inet_prefix *a, int port,
			    unsigned int ifindex, bool v6only)
{
	char buf[1024];
	const char *ap = buf;
	const char *ifname = NULL;

	if (a->family == AF_INET) {
		ap = format_host(AF_INET, 4, a->data);
	} else {
		if (!v6only &&
		    !memcmp(a->data, &in6addr_any, sizeof(in6addr_any))) {
			buf[0] = '*';
			buf[1] = 0;
		} else {
			ap = format_host(a->family, 16, a->data);

			/* Numeric IPv6 addresses should be bracketed */
			if (strchr(ap, ':')) {
				snprintf(buf, sizeof(buf),
					 "[%s]", ap);
				ap = buf;
			}
		}
	}

	if (ifindex)
		ifname = ll_index_to_name(ifindex);

	sock_addr_print(ap, ":", port, ifname);
}

struct aafilter {
	inet_prefix	addr;
	int		port;
	unsigned int	iface;
	__u32		mark;
	__u32		mask;
	struct aafilter *next;
};

static int inet2_addr_match(const inet_prefix *a, const inet_prefix *p,
			    int plen)
{
	if (!inet_addr_match(a, p, plen))
		return 0;

	/* Cursed "v4 mapped" addresses: v4 mapped socket matches
	 * pure IPv4 rule, but v4-mapped rule selects only v4-mapped
	 * sockets. Fair? */
	if (p->family == AF_INET && a->family == AF_INET6) {
		if (a->data[0] == 0 && a->data[1] == 0 &&
		    a->data[2] == htonl(0xffff)) {
			inet_prefix tmp = *a;

			tmp.data[0] = a->data[3];
			return inet_addr_match(&tmp, p, plen);
		}
	}
	return 1;
}

static int unix_match(const inet_prefix *a, const inet_prefix *p)
{
	char *addr, *pattern;

	memcpy(&addr, a->data, sizeof(addr));
	memcpy(&pattern, p->data, sizeof(pattern));
	if (pattern == NULL)
		return 1;
	if (addr == NULL)
		addr = "";
	return !fnmatch(pattern, addr, 0);
}

static int run_ssfilter(struct ssfilter *f, struct sockstat *s)
{
	switch (f->type) {
		case SSF_S_AUTO:
	{
		if (s->local.family == AF_UNIX) {
			char *p;

			memcpy(&p, s->local.data, sizeof(p));
			return p == NULL || (p[0] == '@' && strlen(p) == 6 &&
					     strspn(p+1, "0123456789abcdef") == 5);
		}
		if (s->local.family == AF_PACKET)
			return s->lport == 0 && s->local.data[0] == 0;
		if (s->local.family == AF_NETLINK)
			return s->lport < 0;
		if (s->local.family == AF_VSOCK)
			return s->lport > 1023;

		return is_ephemeral(s->lport);
	}
		case SSF_DCOND:
	{
		struct aafilter *a = (void *)f->pred;

		if (a->addr.family == AF_UNIX)
			return unix_match(&s->remote, &a->addr);
		if (a->port != -1 && a->port != s->rport)
			return 0;
		if (a->addr.bitlen) {
			do {
				if (!inet2_addr_match(&s->remote, &a->addr, a->addr.bitlen))
					return 1;
			} while ((a = a->next) != NULL);
			return 0;
		}
		return 1;
	}
		case SSF_SCOND:
	{
		struct aafilter *a = (void *)f->pred;

		if (a->addr.family == AF_UNIX)
			return unix_match(&s->local, &a->addr);
		if (a->port != -1 && a->port != s->lport)
			return 0;
		if (a->addr.bitlen) {
			do {
				if (!inet2_addr_match(&s->local, &a->addr, a->addr.bitlen))
					return 1;
			} while ((a = a->next) != NULL);
			return 0;
		}
		return 1;
	}
		case SSF_D_GE:
	{
		struct aafilter *a = (void *)f->pred;

		return s->rport >= a->port;
	}
		case SSF_D_LE:
	{
		struct aafilter *a = (void *)f->pred;

		return s->rport <= a->port;
	}
		case SSF_S_GE:
	{
		struct aafilter *a = (void *)f->pred;

		return s->lport >= a->port;
	}
		case SSF_S_LE:
	{
		struct aafilter *a = (void *)f->pred;

		return s->lport <= a->port;
	}
		case SSF_DEVCOND:
	{
		struct aafilter *a = (void *)f->pred;

		return s->iface == a->iface;
	}
		case SSF_MARKMASK:
	{
		struct aafilter *a = (void *)f->pred;

		return (s->mark & a->mask) == a->mark;
	}
		/* Yup. It is recursion. Sorry. */
		case SSF_AND:
		return run_ssfilter(f->pred, s) && run_ssfilter(f->post, s);
		case SSF_OR:
		return run_ssfilter(f->pred, s) || run_ssfilter(f->post, s);
		case SSF_NOT:
		return !run_ssfilter(f->pred, s);
		default:
		abort();
	}
}

/* Relocate external jumps by reloc. */
static void ssfilter_patch(char *a, int len, int reloc)
{
	while (len > 0) {
		struct inet_diag_bc_op *op = (struct inet_diag_bc_op *)a;

		if (op->no == len+4)
			op->no += reloc;
		len -= op->yes;
		a += op->yes;
	}
	if (len < 0)
		abort();
}

static int ssfilter_bytecompile(struct ssfilter *f, char **bytecode)
{
	switch (f->type) {
		case SSF_S_AUTO:
	{
		if (!(*bytecode = malloc(4))) abort();
		((struct inet_diag_bc_op *)*bytecode)[0] = (struct inet_diag_bc_op){ INET_DIAG_BC_AUTO, 4, 8 };
		return 4;
	}
		case SSF_DCOND:
		case SSF_SCOND:
	{
		struct aafilter *a = (void *)f->pred;
		struct aafilter *b;
		char *ptr;
		int  code = (f->type == SSF_DCOND ? INET_DIAG_BC_D_COND : INET_DIAG_BC_S_COND);
		int len = 0;

		for (b = a; b; b = b->next) {
			len += 4 + sizeof(struct inet_diag_hostcond);
			if (a->addr.family == AF_INET6)
				len += 16;
			else
				len += 4;
			if (b->next)
				len += 4;
		}
		if (!(ptr = malloc(len))) abort();
		*bytecode = ptr;
		for (b = a; b; b = b->next) {
			struct inet_diag_bc_op *op = (struct inet_diag_bc_op *)ptr;
			int alen = (a->addr.family == AF_INET6 ? 16 : 4);
			int oplen = alen + 4 + sizeof(struct inet_diag_hostcond);
			struct inet_diag_hostcond *cond = (struct inet_diag_hostcond *)(ptr+4);

			*op = (struct inet_diag_bc_op){ code, oplen, oplen+4 };
			cond->family = a->addr.family;
			cond->port = a->port;
			cond->prefix_len = a->addr.bitlen;
			memcpy(cond->addr, a->addr.data, alen);
			ptr += oplen;
			if (b->next) {
				op = (struct inet_diag_bc_op *)ptr;
				*op = (struct inet_diag_bc_op){ INET_DIAG_BC_JMP, 4, len - (ptr-*bytecode)};
				ptr += 4;
			}
		}
		return ptr - *bytecode;
	}
		case SSF_D_GE:
	{
		struct aafilter *x = (void *)f->pred;

		if (!(*bytecode = malloc(8))) abort();
		((struct inet_diag_bc_op *)*bytecode)[0] = (struct inet_diag_bc_op){ INET_DIAG_BC_D_GE, 8, 12 };
		((struct inet_diag_bc_op *)*bytecode)[1] = (struct inet_diag_bc_op){ 0, 0, x->port };
		return 8;
	}
		case SSF_D_LE:
	{
		struct aafilter *x = (void *)f->pred;

		if (!(*bytecode = malloc(8))) abort();
		((struct inet_diag_bc_op *)*bytecode)[0] = (struct inet_diag_bc_op){ INET_DIAG_BC_D_LE, 8, 12 };
		((struct inet_diag_bc_op *)*bytecode)[1] = (struct inet_diag_bc_op){ 0, 0, x->port };
		return 8;
	}
		case SSF_S_GE:
	{
		struct aafilter *x = (void *)f->pred;

		if (!(*bytecode = malloc(8))) abort();
		((struct inet_diag_bc_op *)*bytecode)[0] = (struct inet_diag_bc_op){ INET_DIAG_BC_S_GE, 8, 12 };
		((struct inet_diag_bc_op *)*bytecode)[1] = (struct inet_diag_bc_op){ 0, 0, x->port };
		return 8;
	}
		case SSF_S_LE:
	{
		struct aafilter *x = (void *)f->pred;

		if (!(*bytecode = malloc(8))) abort();
		((struct inet_diag_bc_op *)*bytecode)[0] = (struct inet_diag_bc_op){ INET_DIAG_BC_S_LE, 8, 12 };
		((struct inet_diag_bc_op *)*bytecode)[1] = (struct inet_diag_bc_op){ 0, 0, x->port };
		return 8;
	}

		case SSF_AND:
	{
		char *a1 = NULL, *a2 = NULL, *a;
		int l1, l2;

		l1 = ssfilter_bytecompile(f->pred, &a1);
		l2 = ssfilter_bytecompile(f->post, &a2);
		if (!l1 || !l2) {
			free(a1);
			free(a2);
			return 0;
		}
		if (!(a = malloc(l1+l2))) abort();
		memcpy(a, a1, l1);
		memcpy(a+l1, a2, l2);
		free(a1); free(a2);
		ssfilter_patch(a, l1, l2);
		*bytecode = a;
		return l1+l2;
	}
		case SSF_OR:
	{
		char *a1 = NULL, *a2 = NULL, *a;
		int l1, l2;

		l1 = ssfilter_bytecompile(f->pred, &a1);
		l2 = ssfilter_bytecompile(f->post, &a2);
		if (!l1 || !l2) {
			free(a1);
			free(a2);
			return 0;
		}
		if (!(a = malloc(l1+l2+4))) abort();
		memcpy(a, a1, l1);
		memcpy(a+l1+4, a2, l2);
		free(a1); free(a2);
		*(struct inet_diag_bc_op *)(a+l1) = (struct inet_diag_bc_op){ INET_DIAG_BC_JMP, 4, l2+4 };
		*bytecode = a;
		return l1+l2+4;
	}
		case SSF_NOT:
	{
		char *a1 = NULL, *a;
		int l1;

		l1 = ssfilter_bytecompile(f->pred, &a1);
		if (!l1) {
			free(a1);
			return 0;
		}
		if (!(a = malloc(l1+4))) abort();
		memcpy(a, a1, l1);
		free(a1);
		*(struct inet_diag_bc_op *)(a+l1) = (struct inet_diag_bc_op){ INET_DIAG_BC_JMP, 4, 8 };
		*bytecode = a;
		return l1+4;
	}
		case SSF_DEVCOND:
	{
		/* bytecompile for SSF_DEVCOND not supported yet */
		return 0;
	}
		case SSF_MARKMASK:
	{
		struct aafilter *a = (void *)f->pred;
		struct instr {
			struct inet_diag_bc_op op;
			struct inet_diag_markcond cond;
		};
		int inslen = sizeof(struct instr);

		if (!(*bytecode = malloc(inslen))) abort();
		((struct instr *)*bytecode)[0] = (struct instr) {
			{ INET_DIAG_BC_MARK_COND, inslen, inslen + 4 },
			{ a->mark, a->mask},
		};

		return inslen;
	}
		default:
		abort();
	}
}

static void proc_ctx_print(struct sockstat *s)
{
    printf("\"users\": [");
	if (show_proc_ctx || show_sock_ctx) {
		find_entry(s->ino,
				(show_proc_ctx & show_sock_ctx) ?
				PROC_SOCK_CTX : PROC_CTX);
	} else if (show_users) {
		find_entry(s->ino, USERS);
	}
    printf("], ");
}

static void inet_stats_print(struct sockstat *s, bool v6only)
{
	sock_state_print(s);

    printf("\"local\": {");
	inet_addr_print(&s->local, s->lport, s->iface, v6only);
    printf("}, ");
    printf("\"remote\": {");
	inet_addr_print(&s->remote, s->rport, 0, v6only);
    printf("}, ");

	proc_ctx_print(s);
}

static void tcp_stats_print(struct tcpstat *s)
{
	if (s->has_ts_opt)
		printf("\"ts\": true, ");
	if (s->has_sack_opt)
		printf("\"sack\": true, ");
	if (s->has_ecn_opt)
		printf("\"ecn\": true, ");
	if (s->has_ecnseen_opt)
		printf("\"ecnseen\": true, ");
	if (s->has_fastopen_opt)
		printf("\"fastopen\": true, ");
	if (s->cong_alg[0])
		printf("\"cong_alg\": \"%s\", ", s->cong_alg);
	if (s->has_wscale_opt) {
		printf("\"snd_wscale\": %d, ", s->rcv_wscale);
		printf("\"rcv_wscale\": %d, ", s->snd_wscale);
    }
	if (s->rto)
		printf("\"rto\": %g, ", s->rto);
	if (s->backoff)
		printf("\"backoff\": %u, ", s->backoff);
	if (s->rtt) {
		printf("\"rtt\": %g, ", s->rtt);
		printf("\"rttvar\": %g, ", s->rttvar);
    }
	if (s->ato)
		printf("\"ato\": %g, ", s->ato);

	if (s->qack)
		printf("\"qack\": %d, ", s->qack);
	if (s->qack & 1)
		printf("\"bidir\": true, ");

	if (s->mss)
		printf("\"mss\": %d, ", s->mss);
	if (s->pmtu)
		printf("\"pmtu\": %u, ", s->pmtu);
	if (s->rcv_mss)
		printf("\"rcvmss\": %d, ", s->rcv_mss);
	if (s->advmss)
		printf("\"advmss\": %d, ", s->advmss);
	if (s->cwnd)
		printf("\"cwnd\": %u, ", s->cwnd);
	if (s->ssthresh)
		printf("\"ssthresh\": %d, ", s->ssthresh);

	if (s->bytes_sent)
		printf("\"bytes_sent\": %llu, ", s->bytes_sent);
	if (s->bytes_retrans)
		printf("\"bytes_retrans\": %llu, ", s->bytes_retrans);
	if (s->bytes_acked)
		printf("\"bytes_acked\": %llu, ", s->bytes_acked);
	if (s->bytes_received)
		printf("\"bytes_received\": %llu, ", s->bytes_received);
	if (s->segs_out)
		printf("\"segs_out\": %u, ", s->segs_out);
	if (s->segs_in)
		printf("\"segs_in\": %u, ", s->segs_in);
	if (s->data_segs_out)
		printf("\"data_segs_out\": %u, ", s->data_segs_out);
	if (s->data_segs_in)
		printf("\"data_segs_in\": %u, ", s->data_segs_in);

	if (s->dctcp && s->dctcp->enabled) {
		struct dctcpstat *dctcp = s->dctcp;

        printf("\"dctcp: {\"");
        printf("\"ce_state\": %u, ", dctcp->ce_state);
        printf("\"alpha\": %u, ", dctcp->alpha);
        printf("\"ab_ecn\": %u, ", dctcp->ab_ecn);
        printf("\"ab_tot\": %u", dctcp->ab_tot);
        printf("}, ");
	} else if (s->dctcp) {
		printf("\"dctcp\": fallback_mode, ");
	}

	if (s->bbr_info) {
		__u64 bw;

		bw = s->bbr_info->bbr_bw_hi;
		bw <<= 32;
		bw |= s->bbr_info->bbr_bw_lo;

        printf("\"bbr\": {");
		printf("\"bw\": %llu, ", bw);
        printf("\"mrtt\": %u, ", s->bbr_info->bbr_min_rtt);
		if (s->bbr_info->bbr_pacing_gain)
			printf("\"pacing_gain\": %u, ", s->bbr_info->bbr_pacing_gain);
		if (s->bbr_info->bbr_cwnd_gain)
			printf("\"cwnd_gain\": %u, ", s->bbr_info->bbr_cwnd_gain);
        printf("}, ");
	}

	if (s->send_bps)
		printf("\"send\": %.0f, ", s->send_bps);
	if (s->lastsnd)
		printf("\"lastsnd\": %u, ", s->lastsnd);
	if (s->lastrcv)
		printf("\"lastrcv\": %u, ", s->lastrcv);
	if (s->lastack)
		printf("\"lastack\": %u, ", s->lastack);

	if (s->pacing_rate) {
		printf("\"pacing_rate\": %.0f, ", s->pacing_rate);
		if (s->pacing_rate_max) {
			printf("\"pacing_rate_max\": %.0f, ", s->pacing_rate_max);
        }
	}

	if (s->delivery_rate)
		printf("\"delivery_rate\": %.0f, ", s->delivery_rate);
	if (s->delivered)
		printf("\"delivered\": %u, ", s->delivered);
	if (s->delivered_ce)
		printf("\"delivered_ce\": %u, ", s->delivered_ce);
	if (s->app_limited)
		printf("\"app_limited\": true, ");

	if (s->busy_time) {
		printf("\"busy\": %llu, ", s->busy_time / 1000);
		if (s->rwnd_limited) {
			printf("\"rwnd_limited\": %llu, ", s->rwnd_limited / 1000);
			printf("\"rwnd_limited_pct\": %.1f%%, ", 100.0 * s->rwnd_limited / s->busy_time);
        }
		if (s->sndbuf_limited) {
			printf("\"sndbuf_limited\": %llu, ", s->sndbuf_limited / 1000);
			printf("\"sndbuf_limited_pct\": %.1f%%, ", 100.0 * s->sndbuf_limited / s->busy_time);
        }
	}

	if (s->unacked)
		printf("\"unacked\": %u, ", s->unacked);
	if (s->retrans || s->retrans_total) {
		printf("\"retrans\": %u, ", s->retrans);
		printf("\"retrans_total\": %u, ", s->retrans_total);
    }
	if (s->lost)
		printf("\"lost\": %u, ", s->lost);
	if (s->sacked && s->ss.state != SS_LISTEN)
		printf("\"sacked\": %u, ", s->sacked);
	if (s->dsack_dups)
		printf("\"dsack_dups\": %u, ", s->dsack_dups);
	if (s->fackets)
		printf("\"fackets\": %u, ", s->fackets);
	if (s->reordering != 3)
		printf("\"reordering\": %d, ", s->reordering);
	if (s->reord_seen)
		printf("\"reord_seen\": %d, ", s->reord_seen);
	if (s->rcv_rtt)
		printf("\"rcv_rtt\": %g, ", s->rcv_rtt);
	if (s->rcv_space)
		printf("\"rcv_space\": %d, ", s->rcv_space);
	if (s->rcv_ssthresh)
		printf("\"rcv_ssthresh\": %u, ", s->rcv_ssthresh);
	if (s->not_sent)
		printf("\"notsent\": %u, ", s->not_sent);
	if (s->min_rtt)
		printf("\"minrtt\": %g, ", s->min_rtt);
}

static void tcp_timer_print(struct tcpstat *s)
{
	static const char * const tmr_name[] = {
		"off",
		"on",
		"keepalive",
		"timewait",
		"persist",
		"unknown"
	};

	if (s->timer) {
		if (s->timer > 4)
			s->timer = 5;
		printf("\"timer\": {\"type\": \"%s\", \"time\": %u, \"retrans\": %d}, ",
			     tmr_name[s->timer],
			     s->timeout,
			     s->retrans);
	}
}

static void print_skmeminfo(struct rtattr *tb[], int attrtype)
{
	const __u32 *skmeminfo;

	if (!tb[attrtype]) {
		if (attrtype == INET_DIAG_SKMEMINFO) {
			if (!tb[INET_DIAG_MEMINFO])
				return;

			const struct inet_diag_meminfo *minfo =
				RTA_DATA(tb[INET_DIAG_MEMINFO]);

			printf(" mem:(r%u,w%u,f%u,t%u)",
				   minfo->idiag_rmem,
				   minfo->idiag_wmem,
				   minfo->idiag_fmem,
				   minfo->idiag_tmem);
		}
		return;
	}

	skmeminfo = RTA_DATA(tb[attrtype]);

	printf("\"skmem\": {\"rmem_alloc\": %u, \"rcvbuf\": %u, \"wmem_alloc\": %u, \"sndbuf\": %u, \"fwd_alloc\": %u, \"wmem_queued\": %u, \"optmem\": %u, ",
		     skmeminfo[SK_MEMINFO_RMEM_ALLOC],
		     skmeminfo[SK_MEMINFO_RCVBUF],
		     skmeminfo[SK_MEMINFO_WMEM_ALLOC],
		     skmeminfo[SK_MEMINFO_SNDBUF],
		     skmeminfo[SK_MEMINFO_FWD_ALLOC],
		     skmeminfo[SK_MEMINFO_WMEM_QUEUED],
		     skmeminfo[SK_MEMINFO_OPTMEM]);

	if (RTA_PAYLOAD(tb[attrtype]) >=
		(SK_MEMINFO_BACKLOG + 1) * sizeof(__u32))
		printf("\"backlog\": %u, ", skmeminfo[SK_MEMINFO_BACKLOG]);

	if (RTA_PAYLOAD(tb[attrtype]) >=
		(SK_MEMINFO_DROPS + 1) * sizeof(__u32))
		printf("\"drops\": %u, ", skmeminfo[SK_MEMINFO_DROPS]);

	printf("}, ");
}

static void print_md5sig(struct tcp_diag_md5sig *sig)
{
	printf("%s/%d=",
	    format_host(sig->tcpm_family,
			sig->tcpm_family == AF_INET6 ? 16 : 4,
			&sig->tcpm_addr),
	    sig->tcpm_prefixlen);
	print_escape_buf(sig->tcpm_key, sig->tcpm_keylen, " ,");
}

#define TCPI_HAS_OPT(info, opt) !!(info->tcpi_options & (opt))

static void tcp_show_info(const struct nlmsghdr *nlh, struct inet_diag_msg *r,
		struct rtattr *tb[])
{
	double rtt = 0;
	struct tcpstat s = {};

	s.ss.state = r->idiag_state;

	print_skmeminfo(tb, INET_DIAG_SKMEMINFO);

	if (tb[INET_DIAG_INFO]) {
		struct tcp_info *info;
		int len = RTA_PAYLOAD(tb[INET_DIAG_INFO]);

		/* workaround for older kernels with less fields */
		if (len < sizeof(*info)) {
			info = alloca(sizeof(*info));
			memcpy(info, RTA_DATA(tb[INET_DIAG_INFO]), len);
			memset((char *)info + len, 0, sizeof(*info) - len);
		} else
			info = RTA_DATA(tb[INET_DIAG_INFO]);

		if (show_options) {
			s.has_ts_opt	   = TCPI_HAS_OPT(info, TCPI_OPT_TIMESTAMPS);
			s.has_sack_opt	   = TCPI_HAS_OPT(info, TCPI_OPT_SACK);
			s.has_ecn_opt	   = TCPI_HAS_OPT(info, TCPI_OPT_ECN);
			s.has_ecnseen_opt  = TCPI_HAS_OPT(info, TCPI_OPT_ECN_SEEN);
			s.has_fastopen_opt = TCPI_HAS_OPT(info, TCPI_OPT_SYN_DATA);
		}

		if (tb[INET_DIAG_CONG])
			strncpy(s.cong_alg,
				rta_getattr_str(tb[INET_DIAG_CONG]),
				sizeof(s.cong_alg) - 1);

		if (TCPI_HAS_OPT(info, TCPI_OPT_WSCALE)) {
			s.has_wscale_opt  = true;
			s.snd_wscale	  = info->tcpi_snd_wscale;
			s.rcv_wscale	  = info->tcpi_rcv_wscale;
		}

		if (info->tcpi_rto && info->tcpi_rto != 3000000)
			s.rto = (double)info->tcpi_rto / 1000;

		s.backoff	 = info->tcpi_backoff;
		s.rtt		 = (double)info->tcpi_rtt / 1000;
		s.rttvar	 = (double)info->tcpi_rttvar / 1000;
		s.ato		 = (double)info->tcpi_ato / 1000;
		s.mss		 = info->tcpi_snd_mss;
		s.rcv_mss	 = info->tcpi_rcv_mss;
		s.advmss	 = info->tcpi_advmss;
		s.rcv_space	 = info->tcpi_rcv_space;
		s.rcv_rtt	 = (double)info->tcpi_rcv_rtt / 1000;
		s.lastsnd	 = info->tcpi_last_data_sent;
		s.lastrcv	 = info->tcpi_last_data_recv;
		s.lastack	 = info->tcpi_last_ack_recv;
		s.unacked	 = info->tcpi_unacked;
		s.retrans	 = info->tcpi_retrans;
		s.retrans_total  = info->tcpi_total_retrans;
		s.lost		 = info->tcpi_lost;
		s.sacked	 = info->tcpi_sacked;
		s.fackets	 = info->tcpi_fackets;
		s.reordering	 = info->tcpi_reordering;
		s.rcv_ssthresh   = info->tcpi_rcv_ssthresh;
		s.cwnd		 = info->tcpi_snd_cwnd;
		s.pmtu		 = info->tcpi_pmtu;

		if (info->tcpi_snd_ssthresh < 0xFFFF)
			s.ssthresh = info->tcpi_snd_ssthresh;

		rtt = (double) info->tcpi_rtt;
		if (tb[INET_DIAG_VEGASINFO]) {
			const struct tcpvegas_info *vinfo
				= RTA_DATA(tb[INET_DIAG_VEGASINFO]);

			if (vinfo->tcpv_enabled &&
					vinfo->tcpv_rtt && vinfo->tcpv_rtt != 0x7fffffff)
				rtt =  vinfo->tcpv_rtt;
		}

		if (tb[INET_DIAG_DCTCPINFO]) {
			struct dctcpstat *dctcp = malloc(sizeof(struct
						dctcpstat));

			const struct tcp_dctcp_info *dinfo
				= RTA_DATA(tb[INET_DIAG_DCTCPINFO]);

			dctcp->enabled	= !!dinfo->dctcp_enabled;
			dctcp->ce_state = dinfo->dctcp_ce_state;
			dctcp->alpha	= dinfo->dctcp_alpha;
			dctcp->ab_ecn	= dinfo->dctcp_ab_ecn;
			dctcp->ab_tot	= dinfo->dctcp_ab_tot;
			s.dctcp		= dctcp;
		}

		if (tb[INET_DIAG_BBRINFO]) {
			const void *bbr_info = RTA_DATA(tb[INET_DIAG_BBRINFO]);
			int len = min(RTA_PAYLOAD(tb[INET_DIAG_BBRINFO]),
				      sizeof(*s.bbr_info));

			s.bbr_info = calloc(1, sizeof(*s.bbr_info));
			if (s.bbr_info && bbr_info)
				memcpy(s.bbr_info, bbr_info, len);
		}

		if (rtt > 0 && info->tcpi_snd_mss && info->tcpi_snd_cwnd) {
			s.send_bps = (double) info->tcpi_snd_cwnd *
				(double)info->tcpi_snd_mss * 8000000. / rtt;
		}

		if (info->tcpi_pacing_rate &&
				info->tcpi_pacing_rate != ~0ULL) {
			s.pacing_rate = info->tcpi_pacing_rate * 8.;

			if (info->tcpi_max_pacing_rate &&
					info->tcpi_max_pacing_rate != ~0ULL)
				s.pacing_rate_max = info->tcpi_max_pacing_rate * 8.;
		}
		s.bytes_acked = info->tcpi_bytes_acked;
		s.bytes_received = info->tcpi_bytes_received;
		s.segs_out = info->tcpi_segs_out;
		s.segs_in = info->tcpi_segs_in;
		s.data_segs_out = info->tcpi_data_segs_out;
		s.data_segs_in = info->tcpi_data_segs_in;
		s.not_sent = info->tcpi_notsent_bytes;
		if (info->tcpi_min_rtt && info->tcpi_min_rtt != ~0U)
			s.min_rtt = (double) info->tcpi_min_rtt / 1000;
		s.delivery_rate = info->tcpi_delivery_rate * 8.;
		s.app_limited = info->tcpi_delivery_rate_app_limited;
		s.busy_time = info->tcpi_busy_time;
		s.rwnd_limited = info->tcpi_rwnd_limited;
		s.sndbuf_limited = info->tcpi_sndbuf_limited;
		s.delivered = info->tcpi_delivered;
		s.delivered_ce = info->tcpi_delivered_ce;
		s.dsack_dups = info->tcpi_dsack_dups;
		s.reord_seen = info->tcpi_reord_seen;
		s.bytes_sent = info->tcpi_bytes_sent;
		s.bytes_retrans = info->tcpi_bytes_retrans;
		tcp_stats_print(&s);
		free(s.dctcp);
		free(s.bbr_info);
	}
	if (tb[INET_DIAG_MD5SIG]) {
		struct tcp_diag_md5sig *sig = RTA_DATA(tb[INET_DIAG_MD5SIG]);
		int len = RTA_PAYLOAD(tb[INET_DIAG_MD5SIG]);

		printf(" md5keys:");
		print_md5sig(sig++);
		for (len -= sizeof(*sig); len > 0; len -= sizeof(*sig)) {
			printf(",");
			print_md5sig(sig++);
		}
	}
}

static void parse_diag_msg(struct nlmsghdr *nlh, struct sockstat *s)
{
	struct rtattr *tb[INET_DIAG_MAX+1];
	struct inet_diag_msg *r = NLMSG_DATA(nlh);

	parse_rtattr(tb, INET_DIAG_MAX, (struct rtattr *)(r+1),
		     nlh->nlmsg_len - NLMSG_LENGTH(sizeof(*r)));

	s->state	= r->idiag_state;
	s->local.family	= s->remote.family = r->idiag_family;
	s->lport	= ntohs(r->id.idiag_sport);
	s->rport	= ntohs(r->id.idiag_dport);
	s->wq		= r->idiag_wqueue;
	s->rq		= r->idiag_rqueue;
	s->ino		= r->idiag_inode;
	s->uid		= r->idiag_uid;
	s->iface	= r->id.idiag_if;
	s->sk		= cookie_sk_get(&r->id.idiag_cookie[0]);

	s->mark = 0;
	if (tb[INET_DIAG_MARK])
		s->mark = rta_getattr_u32(tb[INET_DIAG_MARK]);
	if (tb[INET_DIAG_PROTOCOL])
		s->raw_prot = rta_getattr_u8(tb[INET_DIAG_PROTOCOL]);
	else
		s->raw_prot = 0;

	if (s->local.family == AF_INET)
		s->local.bytelen = s->remote.bytelen = 4;
	else
		s->local.bytelen = s->remote.bytelen = 16;

	memcpy(s->local.data, r->id.idiag_src, s->local.bytelen);
	memcpy(s->remote.data, r->id.idiag_dst, s->local.bytelen);
}

static int inet_show_sock(struct nlmsghdr *nlh,
			  struct sockstat *s)
{
	struct rtattr *tb[INET_DIAG_MAX+1];
	struct inet_diag_msg *r = NLMSG_DATA(nlh);
	unsigned char v6only = 0;

	parse_rtattr(tb, INET_DIAG_MAX, (struct rtattr *)(r+1),
		     nlh->nlmsg_len - NLMSG_LENGTH(sizeof(*r)));

	if (tb[INET_DIAG_PROTOCOL])
		s->type = rta_getattr_u8(tb[INET_DIAG_PROTOCOL]);

	if (s->local.family == AF_INET6 && tb[INET_DIAG_SKV6ONLY])
		v6only = rta_getattr_u8(tb[INET_DIAG_SKV6ONLY]);

    printf("{");

    printf("\"ts\": %llu, ", (unsigned long long)time(NULL));

	inet_stats_print(s, v6only);

	if (show_options) {
		struct tcpstat t = {};

		t.timer = r->idiag_timer;
		t.timeout = r->idiag_expires;
		t.retrans = r->idiag_retrans;
        tcp_timer_print(&t);
	}

	if (show_details) {
		sock_details_print(s);
		if (s->local.family == AF_INET6 && tb[INET_DIAG_SKV6ONLY])
			printf(" v6only:%u", v6only);
	}

	if (show_tos) {
		if (tb[INET_DIAG_TOS])
			printf(" tos:%#x", rta_getattr_u8(tb[INET_DIAG_TOS]));
		if (tb[INET_DIAG_TCLASS])
			printf(" tclass:%#x", rta_getattr_u8(tb[INET_DIAG_TCLASS]));
		if (tb[INET_DIAG_CLASS_ID])
			printf(" class_id:%#x", rta_getattr_u32(tb[INET_DIAG_CLASS_ID]));
	}

	if (show_mem || (show_tcpinfo && s->type == IPPROTO_TCP)) {
        tcp_show_info(nlh, r, tb);
	}
	sctp_ino = s->ino;

    printf("}\n");
    fflush(stdout);

	return 0;
}

static int tcpdiag_send(int fd, int protocol, struct filter *f)
{
	struct sockaddr_nl nladdr = { .nl_family = AF_NETLINK };
	struct {
		struct nlmsghdr nlh;
		struct inet_diag_req r;
	} req = {
		.nlh.nlmsg_len = sizeof(req),
		.nlh.nlmsg_flags = NLM_F_ROOT | NLM_F_MATCH | NLM_F_REQUEST,
		.nlh.nlmsg_seq = MAGIC_SEQ,
		.r.idiag_family = AF_INET,
		.r.idiag_states = f->states,
	};
	char    *bc = NULL;
	int	bclen;
	struct msghdr msg;
	struct rtattr rta;
	struct iovec iov[3];
	int iovlen = 1;

	if (protocol == IPPROTO_UDP)
		return -1;

	if (protocol == IPPROTO_TCP)
		req.nlh.nlmsg_type = TCPDIAG_GETSOCK;
	else
		req.nlh.nlmsg_type = DCCPDIAG_GETSOCK;
	if (show_mem) {
		req.r.idiag_ext |= (1<<(INET_DIAG_MEMINFO-1));
		req.r.idiag_ext |= (1<<(INET_DIAG_SKMEMINFO-1));
	}

	if (show_tcpinfo) {
		req.r.idiag_ext |= (1<<(INET_DIAG_INFO-1));
		req.r.idiag_ext |= (1<<(INET_DIAG_VEGASINFO-1));
		req.r.idiag_ext |= (1<<(INET_DIAG_CONG-1));
	}

	if (show_tos) {
		req.r.idiag_ext |= (1<<(INET_DIAG_TOS-1));
		req.r.idiag_ext |= (1<<(INET_DIAG_TCLASS-1));
	}

	iov[0] = (struct iovec){
		.iov_base = &req,
		.iov_len = sizeof(req)
	};
	if (f->f) {
		bclen = ssfilter_bytecompile(f->f, &bc);
		if (bclen) {
			rta.rta_type = INET_DIAG_REQ_BYTECODE;
			rta.rta_len = RTA_LENGTH(bclen);
			iov[1] = (struct iovec){ &rta, sizeof(rta) };
			iov[2] = (struct iovec){ bc, bclen };
			req.nlh.nlmsg_len += RTA_LENGTH(bclen);
			iovlen = 3;
		}
	}

	msg = (struct msghdr) {
		.msg_name = (void *)&nladdr,
		.msg_namelen = sizeof(nladdr),
		.msg_iov = iov,
		.msg_iovlen = iovlen,
	};

	if (sendmsg(fd, &msg, 0) < 0) {
		close(fd);
		return -1;
	}

	return 0;
}

static int sockdiag_send(int family, int fd, int protocol, struct filter *f)
{
	struct sockaddr_nl nladdr = { .nl_family = AF_NETLINK };
	DIAG_REQUEST(req, struct inet_diag_req_v2 r);
	char    *bc = NULL;
	int	bclen;
	struct msghdr msg;
	struct rtattr rta;
	struct iovec iov[3];
	int iovlen = 1;

	if (family == PF_UNSPEC)
		return tcpdiag_send(fd, protocol, f);

	memset(&req.r, 0, sizeof(req.r));
	req.r.sdiag_family = family;
	req.r.sdiag_protocol = protocol;
	req.r.idiag_states = f->states;
	if (show_mem) {
		req.r.idiag_ext |= (1<<(INET_DIAG_MEMINFO-1));
		req.r.idiag_ext |= (1<<(INET_DIAG_SKMEMINFO-1));
	}

	if (show_tcpinfo) {
		req.r.idiag_ext |= (1<<(INET_DIAG_INFO-1));
		req.r.idiag_ext |= (1<<(INET_DIAG_VEGASINFO-1));
		req.r.idiag_ext |= (1<<(INET_DIAG_CONG-1));
	}

	if (show_tos) {
		req.r.idiag_ext |= (1<<(INET_DIAG_TOS-1));
		req.r.idiag_ext |= (1<<(INET_DIAG_TCLASS-1));
	}

	iov[0] = (struct iovec){
		.iov_base = &req,
		.iov_len = sizeof(req)
	};
	if (f->f) {
		bclen = ssfilter_bytecompile(f->f, &bc);
		if (bclen) {
			rta.rta_type = INET_DIAG_REQ_BYTECODE;
			rta.rta_len = RTA_LENGTH(bclen);
			iov[1] = (struct iovec){ &rta, sizeof(rta) };
			iov[2] = (struct iovec){ bc, bclen };
			req.nlh.nlmsg_len += RTA_LENGTH(bclen);
			iovlen = 3;
		}
	}

	msg = (struct msghdr) {
		.msg_name = (void *)&nladdr,
		.msg_namelen = sizeof(nladdr),
		.msg_iov = iov,
		.msg_iovlen = iovlen,
	};

	if (sendmsg(fd, &msg, 0) < 0) {
		close(fd);
		return -1;
	}

	return 0;
}

struct inet_diag_arg {
	struct filter *f;
	int protocol;
	struct rtnl_handle *rth;
};

static int kill_inet_sock(struct nlmsghdr *h, void *arg, struct sockstat *s)
{
	struct inet_diag_msg *d = NLMSG_DATA(h);
	struct inet_diag_arg *diag_arg = arg;
	struct rtnl_handle *rth = diag_arg->rth;

	DIAG_REQUEST(req, struct inet_diag_req_v2 r);

	req.nlh.nlmsg_type = SOCK_DESTROY;
	req.nlh.nlmsg_flags = NLM_F_REQUEST | NLM_F_ACK;
	req.nlh.nlmsg_seq = ++rth->seq;
	req.r.sdiag_family = d->idiag_family;
	req.r.sdiag_protocol = diag_arg->protocol;
	req.r.id = d->id;

	if (diag_arg->protocol == IPPROTO_RAW) {
		struct inet_diag_req_raw *raw = (void *)&req.r;

		BUILD_BUG_ON(sizeof(req.r) != sizeof(*raw));
		raw->sdiag_raw_protocol = s->raw_prot;
	}

	return rtnl_talk(rth, &req.nlh, NULL);
}

static int show_one_inet_sock(struct nlmsghdr *h, void *arg)
{
	int err;
	struct inet_diag_arg *diag_arg = arg;
	struct inet_diag_msg *r = NLMSG_DATA(h);
	struct sockstat s = {};

	if (!(diag_arg->f->families & FAMILY_MASK(r->idiag_family)))
		return 0;

	parse_diag_msg(h, &s);
	s.type = diag_arg->protocol;

	if (diag_arg->f->f && run_ssfilter(diag_arg->f->f, &s) == 0)
		return 0;

	if (diag_arg->f->kill && kill_inet_sock(h, arg, &s) != 0) {
		if (errno == EOPNOTSUPP || errno == ENOENT) {
			/* Socket can't be closed, or is already closed. */
			return 0;
		} else {
			perror("SOCK_DESTROY answers");
			return -1;
		}
	}

	err = inet_show_sock(h, &s);
	if (err < 0)
		return err;

	return 0;
}

static int inet_show_netlink(struct filter *f, FILE *dump_fp, int protocol)
{
	int err = 0;
	struct rtnl_handle rth, rth2;
	int family = PF_INET;
	struct inet_diag_arg arg = { .f = f, .protocol = protocol };

	if (rtnl_open_byproto(&rth, 0, NETLINK_SOCK_DIAG))
		return -1;

	if (f->kill) {
		if (rtnl_open_byproto(&rth2, 0, NETLINK_SOCK_DIAG)) {
			rtnl_close(&rth);
			return -1;
		}
		arg.rth = &rth2;
	}

	rth.dump = MAGIC_SEQ;
	rth.dump_fp = dump_fp;
	if (preferred_family == PF_INET6)
		family = PF_INET6;

again:
	if ((err = sockdiag_send(family, rth.fd, protocol, f)))
		goto Exit;

	if ((err = rtnl_dump_filter(&rth, show_one_inet_sock, &arg))) {
		if (family != PF_UNSPEC) {
			family = PF_UNSPEC;
			goto again;
		}
		goto Exit;
	}
	if (family == PF_INET && preferred_family != PF_INET) {
		family = PF_INET6;
		goto again;
	}

Exit:
	rtnl_close(&rth);
	if (arg.rth)
		rtnl_close(arg.rth);
	return err;
}

static int tcp_show(struct filter *f)
{
    inet_show_netlink(f, NULL, IPPROTO_TCP);
    return 0;
}

#define MAX_UNIX_REMEMBER (1024*1024/sizeof(struct sockstat))


struct sock_diag_msg {
	__u8 sdiag_family;
};

/* Get stats from sockstat */

struct ssummary {
	int socks;
	int tcp_mem;
	int tcp_total;
	int tcp_orphans;
	int tcp_tws;
	int tcp4_hashed;
	int udp4;
	int raw4;
	int frag4;
	int frag4_mem;
	int tcp6_hashed;
	int udp6;
	int raw6;
	int frag6;
	int frag6_mem;
};

/* Values 'v' and 'V' are already used so a non-character is used */
#define OPT_VSOCK 256

/* Values of 't' are already used so a non-character is used */
#define OPT_TIPCSOCK 257
#define OPT_TIPCINFO 258

#define OPT_TOS 259

/* Values of 'x' are already used so a non-character is used */
#define OPT_XDPSOCK 260

void main() {
    current_filter.states = SS_CONN;
    current_filter.families = FAMILY_MASK(AF_INET) | FAMILY_MASK(AF_INET6);
    current_filter.states = ~(
        (1 << SS_CLOSE) |
        (1 << SS_LISTEN) |
        (1 << SS_CLOSE_WAIT) |
        (1 << SS_FIN_WAIT1)
    );

    user_ent_hash_build();
    while (1) {
        tcp_show(&current_filter);

        sleep(1);
    }

    if (show_users || show_proc_ctx || show_sock_ctx) {
        user_ent_destroy();
    }
}

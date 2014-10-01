SDN_hw1 Jen-Chieh Huang (jh3478)
=======
COMS E6998-10 Fall 2014 Software Defined Networking Homework 1


How to Config Load-Balancing
-----

All you need is to config the following function - 

/* @lfred: the function is used to initialize the web server addressed and accounts */
protected void initWebSvrs() {
    SvrLoadBalance = false;
    m_webSvrIp = IPv4.toIPv4Address(new String("10.0.0.1"));
    m_webSvr.put(Long.valueOf(1), IPv4.toIPv4Address(new String("10.0.0.1")));
    m_webSvr.put(Long.valueOf(2), IPv4.toIPv4Address(new String("10.0.0.2")));
    m_svrStats.put(Long.valueOf(1), Long.valueOf(0));
    m_svrStats.put(Long.valueOf(2), Long.valueOf(0));
}

1. set the SvrLoadBalance to true
2. set up your main server IP (m_webSvrIp) which everyone uses to access the web servers.
3. add all the servers into m_webSvr (Mac, IP) and m_svrStats (Mac, 0)
4. Compile and you are good to go.

Notice
-----
1. It's recommended that running normal tests before enabling load balancing
2. Assumptions
    - Servers should not initiate the connection to the other hosts.
    - inter-server connections will not trigger load-balancing.

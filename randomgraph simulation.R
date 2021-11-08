install.packages("BiocManager")
BiocManager::install(c("RBGL")) 
BiocManager::install("Rgraphviz")
install.packages("pcalg")
install.packages("igraph")
install.packages("combinat")
install.packages("statGraph")
install.packages("arrangements")
library(pcalg)
library(igraph)
library(combinat)
library(statGraph)
library(arrangements)
powerSet <-
  function (x, m, rev = FALSE) 
  {
    if (missing(m)) m = length(x)
    if (m == 0) return(list(x[c()]))
    
    out = list(x[c()])
    if (length(x) == 1) 
      return(c(out, list(x)))
    for (i in seq_along(x)) {
      if (rev) 
        out = c(lapply(out[lengths(out) < m], function(y) c(y, x[i])), out)
      else out = c(out, lapply(out[lengths(out) < m], function(y) c(y, x[i])))
    }
    out
  }
areeq=function(a,b,p)
{
  for(i in 1:length(a[1,]))
    for(j in 1:length(a[1,]))
      if(b[i,j]!=a[p[i],p[j]])
        return(0)
  return(1)
}
areisogr=function(g1,g2)
{
  a1=as.matrix(get.adjacency(g1))
  a2=as.matrix(get.adjacency(g2))
  return(areiso(a1,a2))
}
areisowithany=function(g,G)
{
  for(i in 1:length(G))
    if(areisogr(g,G[i])==1)
      return(1)
  return(0)
}
areiso=function(a,b)
{
  if(length(a[1,])!=length(b[1,]))
    return(0)
  perm=permn(1:length(a[1,]))
  for(i in 1:length(perm))
    if(areeq(a,b,perm[i])==1)
      return(1)
  return(0)
}
indeg=function(a)
{
  c=rep(0,length(a[1,]))
  for(i in 1:length(a[1,]))
    c[i]=sum(a[,i])
  return(sort(c))
}
outdeg=function(a)
{
  c=rep(0,length(a[1,]))
  for(i in 1:length(a[1,]))
    c[i]=sum(a[i,])
  return(sort(c))
}
naiveisogr=function(g1,g2)
{
  a1=as.matrix(get.adjacency(g1))
  a2=as.matrix(get.adjacency(g2))
  return(naiveiso(a1,a2))
}
naiveiso=function(a,b)
{
  if(length(a[1,])!=length(b[1,]))
    return(0)
  a1=indeg(a)
  b1=indeg(b)
  for(i in 1:length(a[1,]))
    if(a1[i]!=b1[i])
      return(0)
  a1=outdeg(a)
  b1=outdeg(b)
  for(i in 1:length(a[1,]))
    if(a1[i]!=b1[i])
      return(0)
  return(1)
}
toadj=function(g)
{
  a=matrix(data=0,nrow=length(g@nodes),ncol=length(g@nodes))
  for(i in 1:length(g@nodes))
  {
    k=as.numeric(g@edgeL[[i]][[1]])
    if(length(k)>1)
      a[i,k]=1
    if(length(k)==1&&k!=i)
      a[i,k]=1
  }
  return(a)
}


outdeg2=function(a)
{
  b=rep(0,length(a[1,]))
  for(i in 1:length(a[1,]))
    b[i]=sum(a[i,])
  return(which(b>=2))
}
duplicable=function(a)
{
  g=graph.adjacency(a, mode = "directed",diag=TRUE)
  b=outdeg2(a)
  d=b
  c=setdiff(1:length(a[1,]),b)
  for(i in 1:length(c))
  {
    t=intersect(setdiff(as.numeric(subcomponent(g,i,mode="out")),i),b)
    if(length(t)>=1)
      d=c(b,i);
  }
  return(d)
}

indeg0=function(a)
{
  b=rep(0,length(a[1,]))
  for(i in 1:length(a[1,]))
    b[i]=sum(a[,i])
  return(which(b==0))
}
outdeg0=function(a)
{
  b=rep(0,length(a[1,]))
  for(i in 1:length(a[1,]))
    b[i]=sum(a[i,])
  return(which(b==0))
}

adjlist_find_paths <- function(a, n, m, path = list()) {
  path <- c(path, list(n))
  if (n == m) {
    return(list(path))
  } else {
    paths = list()
    for (child in a[[n]]) {
      if (!child %in% unlist(path)) {
        child_paths <- adjlist_find_paths(a, child, m, path)
        paths <- c(paths, child_paths)
      }
    }
    return(paths)
  }
}

# Find paths in graph from vertex source to vertex dest.
paths_from_to <- function(graph, source, dest) {
  a <- as_adj_list(graph, mode = "out")
  paths <- adjlist_find_paths(a, source, dest)
  lapply(paths, function(path) {V(graph)[unlist(path)]})
}


exec=function(texc,i,u)
{
  if(i==1)
    return(texc[3,u])
  if(i==2)
    return(texc[2,u])
  if(i>2)
    return(texc[1,u])
}
distnc=function(tdist,i,u)
{
  return(tdist[u,i]+tdist[i,u])
}
ptoset=function(tdist,texc,i,u,k)
{
  return(min(distnc(tdist,i,u)+exec(texc,u,k)))
}
stoset=function(tdist,texc,u,b,k)
{
  x=rep(0,length(u))
  for(i in 1:length(x))
    x[i]=ptoset(tdist,texc,u[i],b,k)
  return(max(x))
}
lento=function(i,A,tdist,texc,p)
{
  x=rep(0,length(p))
  for(k in 1:length(p)){
    if(length((p[[k]]))>1)
      for(j in seq(length(p[[k]]),2))
        x[k]=x[k]+stoset(tdist,texc,A[as.numeric(p[[k]][j])],A[as.numeric(p[[k]][j-1])],as.numeric(p[[k]][j-1]))
    x[k]=x[k]+ptoset(tdist,texc,i,A[as.numeric(p[[k]][1])],as.numeric(p[[k]][1]))
  }
  return(max(x))
}
Dta=rep(0,15)
stDta=rep(0,15)
Dtawodp=rep(0,15)
stDtawodp=rep(0,15)
Dtaold=rep(0,15)
stDtaold=rep(0,15)
timetable=rep(0,15)
timefind=0
for(i in 2:16){
  print(i);
  delt=sample(5:8,1)
  algo=randDAG(delt,delt/3);
  tmp=(i*(i-1)/2)
  a=toadj(algo)
  texc=matrix(data=0,nrow=3,ncol=length(a[1,]))
  texc[1,]=runif(length(a[1,]),0,3)
  texc[2,]=texc[1,]/2
  texc[3,]=texc[2,]/2
  gr=graph.adjacency(a, mode = "directed",diag=TRUE)
  o0=outdeg0(a)
  i0=indeg0(a)
  p=as.list(0)
  for(k in 1:length(i0))
    for(j in 1:length(o0))
      p=c(p,paths_from_to(gr,i0[k],o0[j]))
  p=p[2:length(p)];
  cont=i-1  
  ddat=rep(0,cont)  
  ddatwodp=rep(0,cont)
  ddatold=rep(0,cont)
  tttime=rep(0,cont)
  g2=0
  for(cnt in 1:cont)
  {
    start_time <- Sys.time()
    if(i<tmp)
    {
      n=sample(i:(i*(i-1)/2),1)
    }
    if(i>=tmp)
    {
      n=i-1
    }
    repeat{
      g1 <- erdos.renyi.game(i,n,type="gnm",directed = FALSE)# for network
      f=as.matrix(get.adjacency(g1))
      if(length(clusters(g1)$csize)==1 && cnt==1){
        break
      }
      if(length(clusters(g1)$csize)==1 && cnt!=1)
      {
        if((graph.isomorphic(g1,g2)==FALSE)||i<=3) #can be switched with naiveisogr(g1,g2)
          break
      }
    }
    g2=g1
    ddatp=rep(0,5)  
    ddatwodpp=rep(0,5)
    ddatoldp=rep(0,5)
    for(temp in 1:5){
      #temp=1
      a=toadj(algo)
      o0=outdeg0(a)
      i0=indeg0(a)
      p=as.list(0)
      for(k00 in 1:length(i0))
        for(j00 in 1:length(o0))
          p=c(p,paths_from_to(gr,i0[k00],o0[j00]))
      p=p[2:length(p)];
      fp=matrix(data=0,nrow=length(f[1,])+1,ncol=length(f[1,])+1)
      fp[1,2]=1
      fp[2,1]=1
      fp[2:length(fp[1,]),2:length(fp[1,])]=f
      for(j in 1:length(fp[1,]))
        for(k in 1:length(fp[1,]))
          fp[j,k]=fp[j,k]*(1+abs(rnorm(1,0,1)))
      gp=graph.adjacency(fp, mode = "undirected", weighted = TRUE, diag = FALSE)
      tdist <- shortest.paths(gp, algorithm = "dijkstra")
      x=rep(0,i-1);
      l=rep(1,length(a[1,]))
      lp=l
      for(k in 3:(i+1))
        x[k-2]=lento(k,l,tdist,texc,p)
      y=x
      yp=x
      allcomp=combinations(length(fp[1,]), length(a[1,]), replace=TRUE)
      for(zed in 1:length(allcomp[,1])){
        for(k in 3:(i+1)){
          x[k-2]=lento(k,allcomp[zed,],tdist,texc,p)
          if(y[k-2]>x[k-2]){
            y[k-2]=x[k-2];
          }
        }
        if(sqrt(sum(yp^2))==sqrt(sum(x^2))&&length(which(lp==lp[1]))==length(lp)){
          lp=allcomp[zed,]
        }
        if(sqrt(sum(yp^2))>sqrt(sum(x^2))){
          for(k in 3:(i+1))
            yp[k-2]=x[k-2];
          lp=allcomp[zed,]
        }
      }
      ddatwodpp[temp]=sqrt(sum(yp^2))
      b=duplicable(a)
      lpp=lp
      gr=graph.adjacency(a, mode = "directed",diag=TRUE)
      kap=setdiff(as.numeric(subcomponent(gr,b,mode="out")),b)
      if(length(kap>=1))
        for(jot in 1:length(kap)){
          lpp[b]=lp[kap[jot]]
          for(k in 3:(i+1)){
            x[k-2]=lento(k,lpp,tdist,texc,p)
            if(yp[k-2]>x[k-2]){
              yp[k-2]=x[k-2];
            }
          }
        }
      ddatoldp[temp]=sqrt(sum(yp^2))
      ddatp[temp]=sqrt(sum(y^2))
    }
    ddatwodp[cnt]=mean(ddatwodpp)
    ddatold[cnt]=mean(ddatoldp)
    ddat[cnt]=mean(ddatp)
    end_time <- Sys.time()
    timefind=end_time - start_time
    print(timefind)
    tttime[cnt]=timefind
  }
  timetable[i-1]=mean(tttime)
  Dta[i-1]=mean(ddat);
  stDta[i-1]=sd(ddat)
  Dtawodp[i-1]=mean(ddatwodp);
  stDtawodp[i-1]=sd(ddatwodp)
  Dtaold[i-1]=mean(ddatold);
  stDtaold[i-1]=sd(ddatold)
  print(c(timetable[i-1],Dta[i-1],Dtaold[i-1],Dtawodp[i-1],stDta[i-1],stDtaold[i-1],stDtawodp[i-1]))
}
plot(Dta,type="p",ylim=c(-1,40),xlab="Number of robots",ylab="Time (seconds)",pch=2,col='red',cex=1.5,cex.lab=1.5, cex.axis=1.5)
legend("topleft",c("Mstep","OrrWD","WoD"),pch=c(2,4,5),col=c('red','blue','black'),cex=1.5)
arrows(1:10, Dta-2*stDta,1:10, Dta+2*stDta, length=0.05, angle=90, code=3,col='red',cex=1.5)
lines(Dtaold,type="p",pch=4,col='blue',cex=1.5)
arrows(1:10, Dtaold-2*stDtaold,1:10, Dtaold+2*stDtaold, length=0.05, angle=90, code=3,col='blue',cex=1.5)
lines(Dtawodp,type="p",pch=5,col='black',cex=1.5)
arrows(1:10, Dtawodp-2*stDtawodp,1:10, Dtawodp+2*stDtawodp, length=0.05, angle=90, code=3,col='black',cex=1.5)
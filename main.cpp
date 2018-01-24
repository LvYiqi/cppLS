#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <time.h>
#include <iostream>
#include <assert.h>
//#include <windef.h>

#define MAX 10010
#define MAXK 50
#define HASHNUM 131073
#define INF -99999999
#define BASENUM 100
#define BASETIME 5
#define MIN(x,y) (((x)<(y))?(x):(y))
using namespace std;

int Tabucircle;
int MAXPOINT=200;
const int MAXCIRCLE = 100000;
int MAXTIME = 1000;
float param_alpha = 0.1f;
float param_beta = 0.4f;
int perturbflag=0;
int N,M,K,best_cost,new_cost,improved,lastfrom,lastc1,lastc2,lastto,improvenum,circle,bestcircle;//N表示点总数，K表示团总数
int weight[MAX][MAX],sumweight[MAX];
int randlst[MAX];
int newtabu[MAXK],index[MAXK],backindex[MAXK],bestindex[MAXK];
int T1,T2,finalmovenum;
int ans[MAXK][MAX],p[MAX][MAXK],tabu[MAXK][MAX];//ans[i][0]中存该团内点个数
int bestK,bestans[MAXK][MAX];
int address[MAX],bestaddress[MAX];//表示每个点所在团
char param_filename[1000];
int s1,s2,s3,s0,timetemp,best_time;
//int countnum=0;

int perturbnum[MAX];

typedef struct pnt_heap{
    int p_weight;
    int pnt_add;
};
pnt_heap *heap[MAX][MAX];//heap[i][0]中存i点所在团编号以及所有团数。

typedef struct move_heap{
    int pnum;
    int moveadd;
    int cost_inc;
};
move_heap *moveheap[MAX];

typedef struct pnt_move{
    int pointnum;
    double moved;
};
pnt_move movepoint[MAX];

typedef struct pnt_move2{
    int pointnum;
    int moved;
};
pnt_move2 movepoint2[MAX];

void showUsage(){
	//TODO:
	cout << "Wrong parameter" << endl;
}

void generateRandList(int len,int randlen)
{
    int idx = 0;

	for (idx = 0; idx < len; idx++)
		randlst[idx] = idx;
	for (idx = 0; idx < randlen; idx++)
	{
		int randid = rand() % (len-idx)+idx;
		int tmp = randlst[idx];
		randlst[idx] = randlst[randid];
		randlst[randid] = tmp;
	}
}

void ReadFile(char *s)
{
    FILE *fp=fopen(s,"r");
    int val;
    if(fp==NULL)
    {
        printf("ReadFile failed\n");
        exit(-1);
    }
    fscanf(fp,"%d",&N);
    printf("%d\n",N);
    for(int i=0;i<N;i++)
    {
        weight[i][i]=0;
        for(int j=i;j<N;j++){
            fscanf(fp,"%d",&val);
            weight[i][j]=-val;
            weight[j][i]=weight[i][j];
        }
    }
}

void rewritebest()
{
    int i,j;
    bestK=K;
    for(i=0;i<MAXK;i++)
        for(j=0;j<=ans[i][0];j++)
            bestans[i][j]=ans[i][j];
    for(i=0;i<MAXK;i++) {
        bestindex[i]=index[i];
    }
    for(i=0;i<N;i++)
        bestaddress[i]=address[i];
//    for(i=0;i<HASHNUM;i++)
//        newtabu[i]=0;
    return ;
}

void p_insert(int point,int p_val,int p_add)
{
    int i,j;
    i=++heap[point][0]->p_weight;
//        assert(i==heap[point][0]->p_weight);
    j=i>>1;
    while(i>1&&p_val>heap[point][j]->p_weight)
    {
        heap[point][i]=heap[point][j];
        i=j;
        j>>=1;
    }
    heap[point][i]=(pnt_heap *)malloc(sizeof(pnt_heap));
    heap[point][i]->p_weight=p_val;
    heap[point][i]->pnt_add=p_add;
    return ;
}

void p_delete(int point,int p_add)
{
    int i,j,len=heap[point][0]->p_weight;
    for(i=1;i<=len;i++)
        if(heap[point][i]->pnt_add==p_add)
            break;
    free(heap[point][i]);
    while(1){
        if(i<<1>=len)
        {
            if(i<len) heap[point][i]=heap[point][len];
            heap[point][0]->p_weight--;
            return ;
        }
        j=i<<1;
        j=(heap[point][j]->p_weight>heap[point][j+1]->p_weight)?j:j+1;
        heap[point][i]=heap[point][j];
        i=j;
    }
    return ;
}


void p_change(int point,int p_val,int p_add)
{
    int i,j,temp=0,len=heap[point][0]->p_weight,maxj,rightj;
    pnt_heap *h_temp;
    for(i=1;i<=len;i++)
        if(heap[point][i]->pnt_add==p_add)
            break;
    h_temp=heap[point][i];
    h_temp->p_weight=p_val;
//    assert(heap[point][i]->p_weight==p_val);
    j=i>>1;
    while(i>1&&p_val>heap[point][j]->p_weight)
    {
        temp=1;
        heap[point][i]=heap[point][j];
        i=j;
        j>>=1;
    }
    if(temp)
    {
        heap[point][i]=h_temp;
        return ;
    }
    while(1)
    {
        j=i<<1;rightj=(i<<1)+1;
//        printf("%d %d %d %d\n",i,j,rightj,len);
        maxj=i;
        if(j<=len&&heap[point][i]->p_weight<heap[point][j]->p_weight)
            maxj=j;
        if(rightj<=len&&heap[point][i]->p_weight<heap[point][rightj]->p_weight)
            maxj=rightj;
        if(maxj != i)
        {
            heap[point][i]=heap[point][maxj];
            heap[point][maxj]=h_temp;
            i=maxj;
        }
        else return ;
    }
}

void InitialSolution2()//初始化三十个团
{
    int i,j,temp1,temp;
	s1=time((time_t*)NULL);
    printf("Initial\n");
    for(i=0;i<N;i++){
        ans[i][0]=0;
        for(j=0;j<N;j++)
        {
            p[i][j]=0;
        }
    }
    K=(30>N)?N:30;
    for(i=0;i<N;i++)
    {
        if(i<K)
        {
            ans[i][++ans[i][0]]=i;
            address[i]=i;
        }
        else{
            temp=rand()%30;
            ans[temp][++ans[temp][0]]=i;
            address[i]=temp;
        }
    }
    for(i=0;i<MAXK;i++)
        for(j=0;j<N;j++){
            tabu[i][j]=0;
        }
    for(i=0;i<MAXK;i++){
        index[i]=i;
        backindex[i]=i;
    }
    for(i=0;i<=N;i++)
        for(j=0;j<K;j++)
        {
            p[i][j]=0;
            for(temp1=1;temp1<=ans[j][0];temp1++)
            {
                p[i][j]+=weight[i][ans[j][temp1]];
            }
        }
    for(i=0;i<N;i++)
    {
        free(heap[i][0]);
        heap[i][0]=(pnt_heap *)malloc(sizeof(pnt_heap));
        heap[i][0]->p_weight=0;
        heap[i][0]->pnt_add=address[i];
        for(j=0;j<K;j++)
        {
            p_insert(i,p[i][j],j);
        }
    }
    new_cost=0;
    for(i=0;i<K;i++)
    {
        for(j=1;j<ans[i][0];j++)
        {
            for(temp1=j+1;temp1<=ans[i][0];temp1++)
            {
                new_cost+=weight[ans[i][j]][ans[i][temp1]];
            }
        }
    }
    if(new_cost>best_cost){
        best_cost=new_cost;
        bestcircle=circle;
        rewritebest();
    }
    printf("%d %d\n",new_cost,best_cost);
}

int findBestMove(int &tempt)
{
    int bestinc=INF,point,temp,tempinc,desw,desadd,count=0;
    int i,j,eqcnt=1;
    generateRandList(N,M);
    for(j=0;j<M;j++)
    {
        i=randlst[j];
        if(heap[i][1]->pnt_add == address[i]){
            temp=(heap[i][2]->p_weight>heap[i][3]->p_weight)?2:3;
        }
        else temp=1;
        desw=heap[i][temp]->p_weight;
        desadd=heap[i][temp]->pnt_add;
        if(ans[address[i]][0]>1&&desw<0) {
            temp=0;
            desadd=index[K];
            desw=0;
        }
        tempinc=desw-p[i][address[i]];
        if(tabu[desadd][i]!=newtabu[desadd]||(tempinc+new_cost>best_cost))
        {
            if(bestinc<tempinc)
            {
                bestinc=tempinc;
                point=i;
                tempt=temp;
                eqcnt=1;
            }
            else if(bestinc==tempinc)
            {
                eqcnt++;
                if(rand()%eqcnt==0)
                {
                    point=i;
                    tempt=temp;
                }
            }
        }
    }
    if(bestinc == INF) return -1;
    return point;
}

void MakeMove(int point,int p_add,int des_add)
{
    if(p_add==des_add) return;
    finalmovenum++;
    int i,j,len=ans[p_add][0];
    new_cost+=(p[point][des_add]-p[point][p_add]);
    for(i=1;i<len;i++)
        if(ans[p_add][i]==point)
        {
            ans[p_add][i]=ans[p_add][len];
            break;
        }
    ans[p_add][0]--;
    ans[des_add][++ans[des_add][0]]=point;
    for(i=0;i<N;i++)
    {
        if(i==point) continue;
        p[i][p_add]-=weight[i][point];
        p[i][des_add]+=weight[i][point];
        p_change(i,p[i][p_add],p_add);
        if(ans[des_add][0]>1){
            p_change(i,p[i][des_add],des_add);
        }
    }
    address[point]=des_add;
    if(ans[p_add][0]==0)
    {
        for(i=0;i<N;i++)
            p_delete(i,p_add);
        K--;
        if(backindex[p_add]!=K){
            i=index[K];
            index[backindex[p_add]]=index[K];
            index[K]=p_add;
            backindex[i]=backindex[p_add];
            backindex[p_add]=K;
        }
    }
    if(ans[des_add][0]==1)
    {
        for(i=0;i<N;i++)
            p_insert(i,p[i][des_add],des_add);
    }
}

void Check()
{
    int i,j,k,temp=0;
    for(i=0;i<K;i++)
    {
        for(j=1;j<ans[index[i]][0];j++)
        {
            for(k=j+1;k<=ans[index[i]][0];k++)
                temp+=weight[ans[index[i]][j]][ans[index[i]][k]];
        }
    }
    assert(temp==new_cost);
}

int DescentSearch()
{
    int i,j;
    int temp=0;
    improved=1;

    while(improved)
    {
        improved=0;
        temp++;
        generateRandList(N,M);
        for(j=0;j<M;j++)
        {
            i=randlst[j];
            if(heap[i][1]->p_weight<0&&ans[address[i]][0]>1)
            {
                improved=1;
                MakeMove(i,address[i],index[K++]);
            }
            else if(p[i][address[i]]<heap[i][1]->p_weight){
                improved=1;
                assert(address[i]!=heap[i][1]->pnt_add);
                MakeMove(i,address[i],heap[i][1]->pnt_add);
            }
        }
    }
    if(new_cost>best_cost){
        best_cost=new_cost;
        bestcircle=circle;
        s2=time(NULL);
        best_time=s2-s1;
        rewritebest();
        return 1;
    }
    return 0;
}

void TabuSearch()
{
    int i,j,find,temp;
    int non_improve=0,tcircle=0;
    lastfrom=-1,lastto=-1;
    for(i=0;i<MAXK;i++)
    {
        newtabu[i]=1;
        for(j=0;j<N;j++)
            tabu[i][j]=0;
    }
    while(non_improve<Tabucircle)
    {
        tcircle++;
        find=findBestMove(temp);
        if(find == -1)
        {
            printf("...\n");
			return ;
        }
        lastfrom=address[find];
        if(temp!=0){
            lastto=heap[find][temp]->pnt_add;
        }
        else {lastto=index[K];K++;}
        tabu[lastto][find]=tcircle;
        tabu[lastfrom][find]=tcircle;
        newtabu[lastto]=tcircle;
        newtabu[lastfrom]=tcircle;
        MakeMove(find,lastfrom,lastto);
//        printf("***%d: %d %d\n",find,lastfrom,lastto);
        non_improve++;
        if(new_cost>best_cost)
        {
            Check();
            best_cost=new_cost;
            bestcircle=circle;
            non_improve=0;
        s2=time(NULL);
        best_time=s2-s1;
        rewritebest();
            improvenum++;
        }
    }
    return ;
}

void insertmove(int point,int desadd,int inc)
{
    int i,j,csize=moveheap[0]->cost_inc;
    if(moveheap[0]->pnum<=csize)
    {
		int idx = moveheap[0]->pnum;
		for (; idx > 1 && moveheap[idx/2]->cost_inc > inc; idx = idx / 2)
			moveheap[idx] = moveheap[idx/2];
		moveheap[idx]=(move_heap *)malloc(sizeof(move_heap));
		moveheap[idx]->cost_inc=inc;
		moveheap[idx]->moveadd=desadd;
		moveheap[idx]->pnum=point;
		moveheap[0]->pnum++;
    }
    else{
		if (inc > moveheap[1]->cost_inc){
			moveheap[1]->cost_inc = inc;
            moveheap[1]->moveadd=desadd;
            moveheap[1]->pnum=point;
			int curidx = 1;
			int smalleridx = curidx;
			int end = 0;
			while(!end){
				int left = 2 * curidx;
				int right = 2 * curidx + 1;
				if (left < csize && moveheap[left]->cost_inc < moveheap[smalleridx]->cost_inc){
					smalleridx = left;
				}
				if (right < csize && moveheap[right]->cost_inc < moveheap[smalleridx]->cost_inc){
					smalleridx = right;
				}
				if (smalleridx != curidx){
					//swap the child node with parent node
					move_heap *temp=moveheap[curidx];
					moveheap[curidx]=moveheap[smalleridx];
					moveheap[smalleridx]=temp;
					curidx = smalleridx;
				}else
					end = 1;
			}
		}
    }
}

//*
void Perturb()
{
    int i,j,tempi,tempj,movenum,desadd,bestpart,tempbestpart,inc;
    int csize=10+rand()%(int)(N/20+1);
	int *moved = new int[N];
	memset(moved, 0, sizeof(int) * N);
    movenum=rand()%((int)(param_beta*N))+(int)(param_alpha*N);
    for(j=0;j<movenum;j++)
    {
        moveheap[0]=(move_heap *)malloc(sizeof(move_heap));
        moveheap[0]->pnum=1;
        moveheap[0]->cost_inc=csize;
        generateRandList(N,M);
        for(tempj=0;tempj<M;tempj++)
        {
            i=randlst[tempj];
			if (moved[i] == 1)
				continue;
            if(heap[i][1]->pnt_add!=address[i])
                bestpart=heap[i][1]->pnt_add;
            else{
                if(heap[i][0]->p_weight==2) bestpart=heap[i][2]->pnt_add;
                else
                    bestpart=(heap[i][2]->p_weight>heap[i][3]->p_weight)?heap[i][2]->pnt_add:heap[i][3]->pnt_add;
            }
            inc=p[i][bestpart]-p[i][address[i]];
            insertmove(i,bestpart,inc);
        }
//        if(address[now]==bestpart[now]) continue;
        tempi=moveheap[0]->pnum-1;
        i=rand()%tempi+1;
        MakeMove(moveheap[i]->pnum,address[moveheap[i]->pnum],moveheap[i]->moveadd);
        if(new_cost>best_cost)
        {
            Check();
            best_cost=new_cost;
            bestcircle=circle;
        s2=time(NULL);
        best_time=s2-s1;
        rewritebest();
        }
        moved[moveheap[i]->pnum]=1;
        for(i=0;i<=tempi;i++) free(moveheap[i]);
    }
}

int main(int argc, char **argv)
{
    int i,j,k,tempcost=0,tabuornot;
    circle=0;
//    randlst = new int[N];
//    for (i = 0; i < argc; i++){
//		fprintf(stdout, "%s ", argv[i]);
//	}
//	fprintf(stdout, "\n");
    char s[1000]="p2000-2.txt";
	for (i = 1; i < argc; i+=2){
		if (argv[i][0] != '-' || argv[i][2] != 0){
			showUsage();
			exit(0);
		}else if (argv[i][1] == 'f'){
			strncpy(s, argv[i+1],1000);
		}else if (argv[i][1] == 's'){
			MAXTIME = atoi(argv[i+1]);
		}else if(argv[i][1] == 'a'){
			param_alpha = atof(argv[i+1]);
		}else if (argv[i][1] == 'b'){
			param_beta =  atof(argv[i+1]);
		}else if (argv[i][1] == 't'){
			Tabucircle = atoi(argv[i+1]);
		}else if (argv[i][1] == 'm'){
			MAXPOINT = atoi(argv[i+1]);
		}
	}
	/*check parameters*/
	if (strlen(s) == 0){
		cerr << "No input data" << endl;
		exit(1);
	}
//	printf("%s\n",param_filename);

//    char s[]="charon_busco\\rand500-100.txt";
//    char s[1000]="in2-300n.txt";
//	strncpy(s,param_filename,1000);
//	printf("%s\n",s);
    char buffer[200];

	s0=time((time_t*)NULL);
	ReadFile(s);
	sprintf(buffer,"%s.best",s);
	FILE *outf=fopen(buffer,"a+");
	srand((unsigned)time(NULL));
	M=(MAXPOINT>N)?N:MAXPOINT;
	best_cost=INF;

	improvenum=0;
	perturbflag=0;
	Tabucircle=min(N,1500);
	for(i=0;i<N;i++)
	{
	    sumweight[i]=0;
	    for(j=0;j<N;j++)
	    {
	        sumweight[i]+=weight[i][j]+BASENUM;
	    }
	}
	finalmovenum=0;
	timetemp=0;
    s2=time((time_t*)NULL);
    InitialSolution2();
	while(circle<MAXCIRCLE)
	{
        srand((unsigned)time(NULL));
	    tabuornot=DescentSearch();
            TabuSearch();
        Perturb();
//	    printf("P:%d %d %d\n",K,new_cost,best_cost);
	    circle++;
        s2=time((time_t*)NULL);
        if(s2-s0>MAXTIME) break;
	}
    int tempk=0;
	for(i=0;i<N;i++){
	    tempk=(tempk>=bestaddress[i])?tempk:bestaddress[i];
	}
	for(i=0;i<=MAXK;i++){
        ans[i][0]=0;
        index[i]=bestindex[i];
	}
	for(i=0;i<N;i++){
	    ans[bestaddress[i]][++ans[bestaddress[i]][0]]=i;
	}
	s2=time((time_t*)NULL);

    for(i=0;i<=tempk;i++)
    {
        for(j=1;j<ans[index[i]][0];j++)
        {
            for(k=j+1;k<=ans[index[i]][0];k++)
                tempcost+=weight[ans[index[i]][j]][ans[index[i]][k]];
        }
    }

	assert(tempcost==best_cost);
	printf("^^^ %d %d %d\n",best_cost,bestcircle,best_time);
    fprintf(outf,"%d %d %d\n",best_cost,bestcircle,best_time);
    for(i=0;i<N;i++){
        fprintf(outf,"%d ",bestaddress[i]);
    }
    printf("Tabu:%d\n",improvenum);
    printf("Time:%d\n",s2-s0);
    printf("movenum:%d\n",finalmovenum);
    fprintf(outf,"\n");

    return 0;
}

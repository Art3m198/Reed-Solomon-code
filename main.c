#include <math.h>
#include <stdio.h>
#define mm  4
#define nn  15          /* nn=2**mm -1   ����� ���������,����������� ��������� */
#define tt  3           /* ���������� ������,������� ����� ���� ���������� */
#define kk  9           /* kk = nn-2*tt  */

int pp [mm+1] = { 1, 1, 0, 0, 1} ; /* specify irreducible polynomial coeffts */
int alpha_to [nn+1], index_of [nn+1], gg [nn-kk+1] ;
int recd [nn], data [kk], bb [nn-kk] ;


void generate_gf()
/* �������� ���� �����
*/
 {
   register int i, mask ;

  mask = 1 ;
  alpha_to[mm] = 0 ;
  for (i=0; i<mm; i++)
   { alpha_to[i] = mask ;
     index_of[alpha_to[i]] = i ;
     if (pp[i]!=0)
       alpha_to[mm] ^= mask ;
     mask <<= 1 ;
   }
  index_of[alpha_to[mm]] = mm ;
  mask >>= 1 ;
  for (i=mm+1; i<nn; i++)
   { if (alpha_to[i-1] >= mask)
        alpha_to[i] = alpha_to[mm] ^ ((alpha_to[i-1]^mask)<<1) ;
     else alpha_to[i] = alpha_to[i-1]<<1 ;
     index_of[alpha_to[i]] = i ;
   }
  index_of[0] = -1 ;
 }


void gen_poly()
/*
  ��������� �������� ��� ��������� ������
*/
 {
   register int i,j ;

   gg[0] = 2 ;    /* primitive element alpha = 2  for GF(2**mm)  */
   gg[1] = 1 ;    /* g(x) = (X+alpha) initially */
   for (i=2; i<=nn-kk; i++)
    { gg[i] = 1 ;
      for (j=i-1; j>0; j--)
        if (gg[j] != 0)  gg[j] = gg[j-1]^ alpha_to[(index_of[gg[j]]+i)%nn] ;
        else gg[j] = gg[j-1] ;
      gg[0] = alpha_to[(index_of[gg[0]]+i)%nn] ;     /* gg[0] can never be zero */
    }
   /* ������� gg[] � ��������� ����� ��� �������� ����������� */
   for (i=0; i<=nn-kk; i++)  gg[i] = index_of[gg[i]] ;
 }


void encode_rs()
/*

   ����������� ������ �������� �� ������� data ��������������� �����������
   ������ � ������ bb[] . ����������� ����������� � ������� �������� ������.
    */
 {
   register int i,j ;
   int feedback ;

   for (i=0; i<nn-kk; i++)   bb[i] = 0 ;
   for (i=kk-1; i>=0; i--)
    {  feedback = index_of[data[i]^bb[nn-kk-1]] ;
       if (feedback != -1)
        { for (j=nn-kk-1; j>0; j--)
            if (gg[j] != -1)
              bb[j] = bb[j-1]^alpha_to[(gg[j]+feedback)%nn] ;
            else
              bb[j] = bb[j-1] ;
          bb[0] = alpha_to[(gg[0]+feedback)%nn] ;
        }
       else
        { for (j=nn-kk-1; j>0; j--)
            bb[j] = bb[j-1] ;
          bb[0] = 0 ;
        } ;
    } ;
 } ;



void decode_rs()
/*

   ���������� ���� ���������� ������������� � ���� � ������� recd[i]
   s[i]-������� ��� �������� ������

   */
 {
   register int i,j,u,q ;
   int elp[nn-kk+2][nn-kk], d[nn-kk+2], l[nn-kk+2], u_lu[nn-kk+2], s[nn-kk+1] ;
   int count=0, syn_error=0, root[tt], loc[tt], z[tt+1], err[nn], reg[tt+1] ;


   for (i=1; i<=nn-kk; i++)
    { s[i] = 0 ;
      for (j=0; j<nn; j++)
        if (recd[j]!=-1)
          s[i] ^= alpha_to[(recd[j]+i*j)%nn] ;      /* recd[j] in index form */
/* ��������������� �������� �� �������������� ����� � ���������  */
      if (s[i]!=0)  syn_error=1 ;        /* ��������� ����� 1 - ������ */
      s[i] = index_of[s[i]] ;
    } ;

   if (syn_error)       /* ����������� ������������ ������ */
    {
/*
   ���������� �������������� ������ � ������� ��������� ����������
*/
/* ������������� ��������� ������� */
      d[0] = 0 ;           /* ��������� ����� */
      d[1] = s[1] ;        /* ��������� ����� */
      elp[0][0] = 0 ;      /* ��������� ����� */
      elp[1][0] = 1 ;      /* �������������� ����� */
      for (i=1; i<nn-kk; i++)
        { elp[0][i] = -1 ;   /* ��������� ����� */
          elp[1][i] = 0 ;   /* �������������� ����� */
        }
      l[0] = 0 ;
      l[1] = 0 ;
      u_lu[0] = -1 ;
      u_lu[1] = 0 ;
      u = 0 ;

      do
      {
        u++ ;
        if (d[u]==-1)
          { l[u+1] = l[u] ;
            for (i=0; i<=l[u]; i++)
             {  elp[u+1][i] = elp[u][i] ;
                elp[u][i] = index_of[elp[u][i]] ;
             }
          }
        else
/* ����� ��������� � ���������� ��������� u_lu[q] ��� �������� d[q]!=0 */
          { q = u-1 ;
            while ((d[q]==-1) && (q>0)) q-- ;
/* ��� �������� 1 d[q]  */
            if (q>0)
             { j=q ;
               do
               { j-- ;
                 if ((d[j]!=-1) && (u_lu[q]<u_lu[j]))
                   q = j ;
               }while (j>0) ;
             } ;

/* ������� �������� q ����� d[u]!=0 � u_lu[q] ����������� */
/* �������� ������� ��� ������ �������� */
            if (l[u]>l[q]+u-q)  l[u+1] = l[u] ;
            else  l[u+1] = l[q]+u-q ;

/* ����� ������� elp(x) */
            for (i=0; i<nn-kk; i++)    elp[u+1][i] = 0 ;
            for (i=0; i<=l[q]; i++)
              if (elp[q][i]!=-1)
                elp[u+1][i+u-q] = alpha_to[(d[u]+nn-d[q]+elp[q][i])%nn] ;
            for (i=0; i<=l[u]; i++)
              { elp[u+1][i] ^= elp[u][i] ;
                elp[u][i] = index_of[elp[u][i]] ;  /*�������������� �������� �������� ������� � ��������� �����*/
              }
          }
        u_lu[u+1] = u-l[u+1] ;

/* ������� (u+1) ��������������� */
        if (u<nn-kk)    /* ���������� �� ��������� �������� */
          {
            if (s[u+1]!=-1)
                   d[u+1] = alpha_to[s[u+1]] ;
            else
              d[u+1] = 0 ;
            for (i=1; i<=l[u+1]; i++)
              if ((s[u+1-i]!=-1) && (elp[u+1][i]!=0))
                d[u+1] ^= alpha_to[(s[u+1-i]+index_of[elp[u+1][i]])%nn] ;
            d[u+1] = index_of[d[u+1]] ;    /* ������� d[u+1] � ���� ������� */
          }
      } while ((u<nn-kk) && (l[u+1]<=tt)) ;

      u++ ;
      if (l[u]<=tt)         /* ����������� ����������� ������ */
       {
/* ������ ������� � ���� ������� */
         for (i=0; i<=l[u]; i++)   elp[u][i] = index_of[elp[u][i]] ;

/* ����� ��������������� ������ �������� */
         for (i=1; i<=l[u]; i++)
           reg[i] = elp[u][i] ;
         count = 0 ;
         for (i=1; i<=nn; i++)
          {  q = 1 ;
             for (j=1; j<=l[u]; j++)
              if (reg[j]!=-1)
                { reg[j] = (reg[j]+j)%nn ;
                  q ^= alpha_to[reg[j]] ;
                } ;
             if (!q)
              { root[count] = i;
                loc[count] = nn-i ;
                count++ ;
              };
          } ;
         if (count==l[u])    /* ���� ���������� ������ ������ �������� tt  */
          {
/* �������������� ����� z(x) */
           for (i=1; i<=l[u]; i++)        /* Z[0] = 1 always - do not need */
            { if ((s[i]!=-1) && (elp[u][i]!=-1))
                 z[i] = alpha_to[s[i]] ^ alpha_to[elp[u][i]] ;
              else if ((s[i]!=-1) && (elp[u][i]==-1))
                      z[i] = alpha_to[s[i]] ;
                   else if ((s[i]==-1) && (elp[u][i]!=-1))
                          z[i] = alpha_to[elp[u][i]] ;
                        else
                          z[i] = 0 ;
              for (j=1; j<i; j++)
                if ((s[j]!=-1) && (elp[u][i-j]!=-1))
                   z[i] ^= alpha_to[(elp[u][i-j] + s[j])%nn] ;
              z[i] = index_of[z[i]] ;         /* �������������� � ��������� ����� */
            } ;

  /* ����������� ������ � ������ �� ������� �������,� ������� �������� ������ loc[i] */
           for (i=0; i<nn; i++)
             { err[i] = 0 ;
               if (recd[i]!=-1)        /* ������� recd[] � �������������� ����� */
                 recd[i] = alpha_to[recd[i]] ;
               else  recd[i] = 0 ;
             }
           for (i=0; i<l[u]; i++)    /* ����������� ����� ������ */
            { err[loc[i]] = 1;
              for (j=1; j<=l[u]; j++)
                if (z[j]!=-1)
                  err[loc[i]] ^= alpha_to[(z[j]+j*root[i])%nn] ;
              if (err[loc[i]]!=0)
               { err[loc[i]] = index_of[err[loc[i]]] ;
                 q = 0 ;
                 for (j=0; j<l[u]; j++)
                   if (j!=i)
                     q += index_of[1^alpha_to[(loc[j]+root[i])%nn]] ;
                 q = q % nn ;
                 err[loc[i]] = alpha_to[(err[loc[i]]-q+nn)%nn] ;
                 recd[loc[i]] ^= err[loc[i]] ;  /*recd[i] ������ ���� � �������������� �����*/
               }
            }
          }
         else    /* no. roots != degree of elp => >tt errors and cannot solve */
           for (i=0; i<nn; i++)        /* ��� ����������� �������� ������� ����� ������ */
               if (recd[i]!=-1)        /* ������� recd[] � ������� */
                 recd[i] = alpha_to[recd[i]] ;
               else  recd[i] = 0 ;     /* �� ������ ������� ����� */
       }
     else         /* ���� ������� ������ ����� tt ��������� ���������� */
       for (i=0; i<nn; i++)       /* ��� ����������� �������� ������� ����� ������ */
          if (recd[i]!=-1)        /* ������� recd[] � ������� */
            recd[i] = alpha_to[recd[i]] ;
          else  recd[i] = 0 ;     /* �� ������ ������� ����� */
    }
   else       /* ���������� �������� => ��� ������: �� ������ ������� ����� */
    for (i=0; i<nn; i++)
       if (recd[i]!=-1)        /* ������� recd[] � ������� */
         recd[i] = alpha_to[recd[i]] ;
       else  recd[i] = 0 ;
 }



int main()
{
  register int i;

/* �������� ���� �����  */
  generate_gf() ;
  printf("Look-up tables for GF(2**%2d)\n",mm) ;
  printf("  i   alpha_to[i]  index_of[i]\n") ;
  for (i=0; i<=nn; i++)
   printf("%3d      %3d          %3d\n",i,alpha_to[i],index_of[i]) ;
  printf("\n\n") ;

/* �������� ��������������� �������� ��� ���� */
  gen_poly() ;


/* ��������������� ��������� ������� ������ ����� �����������. ������ � ����� ��������.
*/
for  (i=0; i<kk; i++)   data[i] = 0 ;

/* ��� ������� ���������� �������� ��������� ��������� */
data[0] = 8 ;
data[1] = 6 ;
data[2] = 8 ;
data[3] = 1 ;
data[4] = 2 ;
data[5] = 4 ;
data[6] = 15 ;
data[7] = 9 ;
data[8] = 9 ;

/* ��������� ������
*/
  encode_rs() ;

/* ������ �������� ����� � ������ recd[] */
  for (i=0; i<nn-kk; i++)  recd[i] = bb[i] ;
  for (i=0; i<kk; i++) recd[i+nn-kk] = data[i] ;


/* ���������� ���������� ��������� ������������ ������ */
  data[nn-nn/2] = 3 ;


  for (i=0; i<nn; i++)
     recd[i] = index_of[recd[i]] ;          /* ������� recd[i] � ��������� ����� */

/* ������������� recv[] */
  decode_rs() ;         /* recd[] ��������� � ������� */


  printf("Results for Reed-Solomon code (n=%3d, k=%3d, t= %3d)\n\n",nn,kk,tt) ;
  printf("  i  data[i]   recd[i](decoded)   (data, recd in polynomial form)\n");
  for (i=0; i<nn-kk; i++)
    printf("%3d    %3d      %3d\n",i, bb[i], recd[i]) ;
  for (i=nn-kk; i<nn; i++)
    printf("%3d    %3d      %3d\n",i, data[i-nn+kk], recd[i]) ;
}

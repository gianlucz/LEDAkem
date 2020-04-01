from scipy import stats
import locale
import subprocess
import shlex
import os

#calculate mean and var for eeach prime calling c program#
primes = ['7547', '7853', '14341', '14939', '16067', '22691', '25693',
    '27437', '35899', '36877', '52147', '57899', '89051', '96221', '152267']

if(os.path.isfile('pval.txt')):
    os.remove('pval.txt')

for p in primes:
    c_prog = ("./inverse_bench_" + p + " 0.05")
    commands = shlex.split(c_prog)

    proc1 = subprocess.Popen(commands)
    proc1.wait()

#start pvalue part#
f_in = open('pval.txt', 'r');
f_out = open('res_pval.txt', 'w');


for p in primes: #(0,15)
    prime = f_in.readline()

    print('\multicolumn{7}{|c|}{ %i }'%(locale.atoi(prime)))
    print('x & pol_avg & pol_var & mon_avg & mon_var & T & pval')

    f_out.write('\multicolumn{7}{|c|}{ %i }\n'%(locale.atoi(prime)))
    f_out.write('x & pol_avg & pol_var & mon_avg & mon_var & T & pval\n')


#    alpha = 0.001
    for l in range(0,6):
        line = f_in.readline()
        (x, pol_avg, pol_var, mon_avg, mon_var, t)= line.split()

        pval = stats.t.sf(abs(locale.atof(t)), 198)*2

        print(x + ' & ' + pol_avg + ' & '+ pol_var + ' & ' + mon_avg+ ' & '+ mon_var + ' & ' + t + ' & %6.4f'%(pval))
        f_out.write(x + ' & ' + pol_avg + ' & '+ pol_var + ' & ' + mon_avg+ ' & '+ mon_var + ' & ' + t + ' & %6.4f\n'%(pval))


    print("\n")
    f_out.write("\n")


f_in.close()
f_out.close()

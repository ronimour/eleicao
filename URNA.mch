/* URNA
 * Author: RONICELI, JORGE
 * Creation date: 15/05/2013
 * Last update: 27/05/2013
 */
MACHINE
    URNA(CANDIDATOS,secao_num)  
    SETS ESTADOS = {PRE_EXECUCAO, EXECUCAO, FINALIZADO} 
    CONSTRAINTS secao_num : NAT      
    VARIABLES  votos, secao_da_urna, ELEITORES_DA_URNA, estado_atual 
    INCLUDES ELEITORADO
    INVARIANT  estado_atual : ESTADOS
               & secao_da_urna = secao_num
               & votos : CANDIDATOS --> NAT   
               & ELEITORES_DA_URNA <: ELEITORES
    INITIALISATION secao_da_urna := secao_num 
                    || votos := CANDIDATOS * {0}
                    || ELEITORES_DA_URNA := dom(secao |> {secao_da_urna})
                    || estado_atual := PRE_EXECUCAO
    OPERATIONS 
    zeresima =  
    PRE !xx.( xx:CANDIDATOS => votos(xx) = 0) & estado_atual = PRE_EXECUCAO THEN
       estado_atual := EXECUCAO 
    END;
    votar(cc,ee) = 
    PRE cc : CANDIDATOS & ee : ELEITORES_DA_URNA & estado_atual = EXECUCAO & votos(cc) < MAXINT THEN
        votos(cc):= votos(cc) + 1 
        ||ELEITORES_DA_URNA := ELEITORES_DA_URNA - {ee} 
    END;
    
    finalizar = 
    PRE estado_atual = EXECUCAO THEN
        estado_atual := FINALIZADO
    END;    
    
    ss <-- votos_do_candidato(cc) = 
    PRE cc : CANDIDATOS & ss: NAT THEN
      ss := votos(cc)  
    END;
    
    ss <-- total_de_votos = 
    BEGIN
      ss := card(dom(secao |> {secao_num})) - card(ELEITORES_DA_URNA)  
    END
    
    
END

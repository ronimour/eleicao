/* ELEICAO
 * Author: RONICELI, JORGE
 * Creation date: 15/05/2013
 * Last update: 27/05/2013
 */
MACHINE
    ELEICAO
    SETS CANDIDATOS;
    ESTADOS_ELEICAO = {PRE_INICIO, INICIADA, FINALIZADA, CONTANDO_VOTOS, VOTOS_CONTADOS}   
    VARIABLES  votos, estado_atual
    INCLUDES Primeira.URNA(CANDIDATOS,1), 
             Segunda.URNA(CANDIDATOS,2),
             Terceira.URNA(CANDIDATOS,3)    
    INVARIANT votos : CANDIDATOS --> NAT
              & estado_atual : ESTADOS_ELEICAO
              & Primeira.ELEITORES_DA_URNA /\ Segunda.ELEITORES_DA_URNA  = {}
              & Primeira.ELEITORES_DA_URNA /\ Terceira.ELEITORES_DA_URNA = {}
              & Segunda.ELEITORES_DA_URNA  /\ Terceira.ELEITORES_DA_URNA = {}
              
    INITIALISATION votos := CANDIDATOS * {0} 
        || estado_atual := PRE_INICIO 
       
     
     OPERATIONS
         iniciar =
         PRE estado_atual = PRE_INICIO THEN
            Primeira.zeresima 
            || Segunda.zeresima 
            || Terceira.zeresima
            || estado_atual := INICIADA
         END;
         
         finalizar =
         PRE estado_atual = INICIADA THEN
             Primeira.finalizar 
            || Segunda.finalizar 
            || Terceira.finalizar 
            || estado_atual := FINALIZADA
         END;
         
         /*contar_votos =
         PRE estado_atual = CONTANDO_VOTOS THEN
                  votos := %xx.( xx:CANDIDATOS | Primeira.votos_do_candidato(xx)
                 + Segunda.votos_do_candidato(xx)
                 + Terceira.votos_do_candidato(xx))
                 
         END;
         */
         cc <-- candidato_eleito =
         PRE estado_atual = VOTOS_CONTADOS THEN
             cc :: dom(votos |> {max(ran(votos))})              
         END
             
END

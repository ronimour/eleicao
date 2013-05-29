/* ELEITORADO
 * Author: RONICELI, JORGE
 * Creation date: 27/05/2013
 */
MACHINE
    ELEITORADO
    SETS ELEITORES
    VARIABLES secao
    INVARIANT secao : ELEITORES --> NAT 
    INITIALISATION ANY XX,YY,ZZ WHERE 
                       XX <: ELEITORES 
                       & YY <: ELEITORES 
                       & ZZ <: ELEITORES 
                       & XX /\ YY = {} 
                       & YY /\ ZZ = {} 
                       & XX /\ ZZ = {}
                       //prova o caso da cardinalidade de ELEITORES ser par
                       // a restricao nao deixa dividir em subconjuntos de mesma cardinalidade
                      & (
                          card(ELEITORES) mod 2 = 0 =>  
                           (card(XX) /= card(YY) or card(YY) /= card(ZZ) or card(XX) /= card(ZZ) )
                         )
                       & XX \/ YY \/ ZZ = ELEITORES
                   THEN 
                       secao:= XX*{1} \/ YY*{2} \/ ZZ*{3} 
                   END
        
END

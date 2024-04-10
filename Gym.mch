MACHINE Gym
    
CONSTANTS         
    mes
    
SETS 
    MATRICULA; NOME; STATUS = { pago, naopago, inadiplente }
    
PROPERTIES        
    mes =3 & card(MATRICULA) <= MAXINT
    
VARIABLES         
    matriculado, statuspagamento, dias, historicopagamento
    
INVARIANT
    matriculado : MATRICULA >+> NOME 
    & statuspagamento : MATRICULA +-> STATUS
    & historicopagamento : MATRICULA +-> 1..30
    & dias : 1..30
    
INITIALISATION
    matriculado := {}
    || statuspagamento := {}
    || dias := 1
    || historicopagamento := MATRICULA  * {1}
    
OPERATIONS
    checkin(mm,nn) =
    PRE mm:MATRICULA & nn:NOME & mm /: dom(matriculado) & nn /: ran(matriculado) 
    THEN matriculado(mm):=nn || statuspagamento(mm):=pago ||historicopagamento(mm):=1
    END;
    
    checkout(mm) = 
    PRE mm : MATRICULA
        & mm : dom(matriculado)
        & matriculado - {mm |-> matriculado(mm)} : MATRICULA >+> NOME
    THEN matriculado := matriculado - {mm |-> matriculado(mm)}
    END;
    
    passardia =
    PRE 1=1
    THEN
        IF !xx . (xx : ran(historicopagamento) => xx<mes)
        THEN dias := dias+1
            || historicopagamento := {xx, vv | xx : dom(matriculado) & vv = historicopagamento(xx) + 1}
        ELSE
            IF !xx . (xx : ran(historicopagamento) => xx=mes)
            THEN  statuspagamento := {xx, ss | xx : dom(matriculado)
                    & ss = {naopago}}
            END
        END
    END;
    
    pagar(mm) =
    PRE mm : MATRICULA & mm : dom(statuspagamento)
    THEN statuspagamento(mm) := pago
    END;
    
    dd <-- queryday(mm) =
    PRE mm : MATRICULA & mm : dom(matriculado)
    THEN dd := historicopagamento(mm)
    END;
    
    rr <-- pagamenttquery(mm) =
    PRE mm : MATRICULA & mm : dom(matriculado)
    THEN
        IF mm : dom(statuspagamento)
        THEN rr := statuspagamento(mm)
        END
    END

END

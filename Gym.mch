MACHINE Gym
    
CONSTANTS       
    mes,max_series,max_rep,max_peso,serie
    
SETS
    MATRICULA; 
    NOME ;
    STATUS = {pago, naopago,inadiplente}; 
    TREINO = {treino1,treino2,treino3,treino4};
    FREQUENCIA = {true,false};
    DIAS={seg,ter,quar,quin};//,sex,sab,domi};
    UNIDADE={kg,minuto};
    TIPO={Agachamento, Supino, Barrafixa}//, Puxadanapolia, Elevacaolateral, Remada, Cadeiraextensora, Abdominalcrunch, Flexaodebraço, Legpress} 
    
PROPERTIES      
    mes = 3 & 
    card(MATRICULA) <= MAXINT &
    max_series = 1..1 &
    max_rep = 1..1 &
    max_peso = 1..1 &
    serie = seq(TIPO*max_series*max_rep*max_peso*UNIDADE)
    
VARIABLES       
    matriculado, statuspagamento, historicopagamento ,treinando, frequencia, controlefrequencia,treinos,dia
    
INVARIANT       
    matriculado: MATRICULA >+>NOME
    & statuspagamento: MATRICULA +-> STATUS
    & historicopagamento: MATRICULA +-> 1..mes
    & treinando: MATRICULA +-> TREINO
    &frequencia: MATRICULA --> 0..mes
    &controlefrequencia: MATRICULA +-> FREQUENCIA
    & treinos:MATRICULA*DIAS +-> serie
    & dia<:DIAS
    
    
INITIALISATION  
    matriculado := {} || statuspagamento := {} || historicopagamento := MATRICULA *{1} || treinando := {}|| frequencia := MATRICULA*{0} || controlefrequencia := MATRICULA*{false}||treinos:={}||dia:={}
    
OPERATIONS
    
    checking(mm)=
    PRE mm:MATRICULA & mm/:dom(treinando) &mm: dom(matriculado) &controlefrequencia(mm)=false &statuspagamento(mm)=pago
    THEN ANY tt WHERE tt:TREINO
        THEN treinando:= treinando \/ {mm|->tt} ||frequencia(mm):=frequencia(mm)+1||controlefrequencia(mm):=true
        END  
    END;
    
    checkout(mm)=
    PRE mm:MATRICULA &mm:dom(matriculado) & mm: dom(treinando) & treinando - {mm |-> treinando(mm)} : MATRICULA +-> TREINO
    THEN treinando:= treinando - {mm|->treinando(mm)}
    END;
    
    matricular(mm,nn) =
    PRE mm:MATRICULA & nn:NOME & mm /: dom(matriculado) & nn /: ran(matriculado)
    THEN matriculado(mm):=nn || statuspagamento(mm):=pago ||historicopagamento(mm):=1
    END;
    
    removermatricula(mm) =
    PRE mm:MATRICULA & mm:dom(matriculado) & matriculado - {mm |-> matriculado(mm)} : MATRICULA >+> NOME
    THEN matriculado:= matriculado -{mm|->matriculado(mm)} || statuspagamento:= statuspagamento -{mm|->statuspagamento(mm)} || historicopagamento:=historicopagamento - {mm|->historicopagamento(mm)} || frequencia(mm):=0
    END;
    
    passardia=
    PRE  { xx,vv | xx : dom(matriculado) & vv = historicopagamento(xx) + 1 } : MATRICULA +-> 1 .. 30
        & { xx,ss | xx : dom(matriculado) &  ss = naopago } : MATRICULA +-> STATUS
        & { xx,vv | xx : dom(matriculado) & vv = 1 } : MATRICULA +-> 1 .. 30 
    THEN 
        IF #xx. (xx : dom(historicopagamento) & historicopagamento(xx)<mes )
        THEN  historicopagamento := historicopagamento <+ ({xx, vv | xx: dom(matriculado) & historicopagamento(xx)<mes&vv=historicopagamento(xx)+1}\/ {xx,vv | xx: dom(matriculado) & historicopagamento(xx)=mes & vv=1} )
            ||statuspagamento := statuspagamento <+ {xx,ss | xx:dom(matriculado) & historicopagamento(xx)=mes &statuspagamento(xx)/=inadiplente &ss=naopago} <+ {xx,ss|xx:dom(matriculado) & historicopagamento(xx)=mes & statuspagamento(xx)=naopago & ss=inadiplente}
            || controlefrequencia := {xx, vv | xx: dom(frequencia) & vv=false} || treinando:= {}
            
        END
    END;
    
    
    pagar(mm)=
    PRE mm:MATRICULA 
        & mm: dom(statuspagamento) 
        & statuspagamento <+ {mm |-> pago} : MATRICULA +-> STATUS
        & statuspagamento(mm) /= pago
    THEN statuspagamento(mm) := pago || historicopagamento(mm) := 1
    END;
    
    dd<-- queryday(mm)=
    PRE mm:MATRICULA & mm: dom(matriculado) & mm:dom(historicopagamento)
    THEN dd:= historicopagamento(mm)
    END;
    
    rr <-- pagamentquery(mm) =
    PRE mm : MATRICULA & mm: dom(matriculado)
    THEN IF mm : dom(statuspagamento)
        THEN rr := statuspagamento(mm)
        END
    END;
    
    addtreino(pp,dd,ss)=
    PRE pp: MATRICULA
        & dd:DIAS
        & ss:serie
        & matriculado(pp) /: {}
        & treinos \/ {pp |-> dd |-> ss} : MATRICULA * DIAS +-> serie
    THEN treinos := treinos \/ {pp |-> dd |-> ss}
    END;
    
    addserie(pp, dd, ss) = 
    PRE pp : MATRICULA
        & dd : DIAS
        & ss : serie
        & pp : dom(matriculado)
        & treinos \/ {pp |-> dd |-> ss} : MATRICULA * DIAS +-> serie
    THEN treinos := treinos \/ {pp |-> dd |-> ss}
    END;
    
    removertreino(pp,dd)=
    PRE pp : MATRICULA & dd : DIAS
        & matriculado(pp) /: {}
        & (pp |-> dd) : dom(treinos)    
    THEN treinos := treinos - {xx, vv | xx: dom(treinos) & xx=pp |-> dd & vv = treinos(pp|->dd)}
    END;
    
    removeserie(pp, dd, ss) =
    PRE pp : MATRICULADO
        & dd : DIAS
        & ss : serie
    THEN
    END
    
END

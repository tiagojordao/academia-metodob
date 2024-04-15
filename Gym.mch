MACHINE Gym
  
CONSTANTS        
   mes
  
SETS
   MATRICULA; NOME ;STATUS = {pago, naopago,inadiplente}; TREINO = {treino1,treino2,treino3,treino4}; FREQUENCIA = {true,false}
  
PROPERTIES       
   mes = 3 & card(MATRICULA) <= MAXINT
  
VARIABLES        
   matriculado, statuspagamento, historicopagamento ,treinando, dias, frequencia, controlefrequencia
  
INVARIANT        
   matriculado: MATRICULA >+>NOME
   & statuspagamento: MATRICULA +-> STATUS
   & historicopagamento: MATRICULA +-> 1..mes
   & treinando: MATRICULA +-> TREINO 
   & dias: 1..mes
   &dias <= mes
   &frequencia: MATRICULA --> 0..mes
   &controlefrequencia: MATRICULA +-> FREQUENCIA
  
INITIALISATION   
   matriculado := {} || statuspagamento := {} || historicopagamento := MATRICULA *{1} || treinando := {} || dias := 1 || frequencia := MATRICULA*{0} || controlefrequencia := MATRICULA*{false}
  
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
   THEN matriculado:= matriculado -{mm|->matriculado(mm)}
   END;
  
   passardia=
   PRE  { xx,vv | xx : dom(matriculado) & vv = historicopagamento(xx) + 1 } : MATRICULA +-> 1 .. 30
       & { xx,ss | xx : dom(matriculado) &  ss = naopago } : MATRICULA +-> STATUS
       & { xx,vv | xx : dom(matriculado) & vv = 1 } : MATRICULA +-> 1 .. 30
   THEN
       IF !xx. (xx : dom(historicopagamento) => historicopagamento(xx)<mes)
       THEN  historicopagamento := {xx, vv | xx: dom(matriculado) & vv=historicopagamento(xx)+1}
           || dias := dias+1
           || controlefrequencia := {xx, vv | xx: dom(frequencia) & vv=false}
       ELSE
           IF #xx. (xx: dom(historicopagamento)  & historicopagamento(xx)=mes)
           THEN statuspagamento := {xx,ss | xx:dom(matriculado) &  ss=naopago}
               ||  historicopagamento := {xx,vv | xx: dom(matriculado) & historicopagamento(xx)=mes & vv=1+dias-historicopagamento(xx)}
               || dias := 1
               ||controlefrequencia := {xx,vv | xx: dom(frequencia) & vv=false}
           END
       END
   END;
  
  
   pagar(mm)=
   PRE mm:MATRICULA & mm: dom(statuspagamento) & statuspagamento <+ {mm |-> pago} : MATRICULA +-> STATUS
   THEN statuspagamento(mm):= pago
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
   END
  
END


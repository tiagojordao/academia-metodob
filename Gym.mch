MACHINE Gym
    
CONSTANTS       
    mes, // Constante para representar o número de meses
    max_series, // Constante para o limite máximo de séries
    max_rep, // Constante para o limite máximo de repetições
    max_peso,  // Constante para o limite máximo de peso
    serie  // Constante para representar a estrutura de uma série de treino
    
SETS
    MATRICULA;  // Conjunto para representar as matrículas
    NOME;  // Conjunto para representar os nomes
    STATUS = {pago, naopago, inadimplente};  // Conjunto para representar os status de pagamento
    TREINO = {treino1, treino2, treino3, treino4};  // Conjunto para representar os tipos de treino
    FREQUENCIA = {true, false};  // Conjunto para representar a frequência (verdadeiro/falso)
    DIAS = {seg, ter, qua, qui, sex, sab};  // Conjunto para representar os dias da semana
    UNIDADE = {kg, minuto};  // Conjunto para representar as unidades de medida
    TIPO = {Agachamento, Supino, Barrafixa, Puxadanapolia}  // Conjunto para representar os tipos de exercícios
    
PROPERTIES      
    mes = 3  // Duração do mês = 3 dias (melhor simulação)
    & card(MATRICULA) <= MAXINT  // Limita o número de matriculas em maxInt
    & max_series = 1..15  // O limite máximo de séries está entre 1 e 15
    & max_rep = 1..15  // O limite máximo de repetições está entre 1 e 15
    & max_peso = 1..30  // O limite máximo de peso está entre 1 e 30
    & serie = seq(TIPO*max_series*max_rep*max_peso*UNIDADE)  // A estrutura de uma série é uma sequência de tipos, séries, repetições, pesos e unidades
    
VARIABLES       
    matriculado,  // armazenar as matrículas
    statuspagamento,  // armazenar o status de pagamento
    historicopagamento,  // armazenar o histórico de pagamento
    treinando,  // armazenar os treinos em andamento
    frequencia,  // definir relação de matricula com cada dia do mês
    controlefrequencia,  // controlar a frequência dos alunos
    treinos,  // armazenar os treinos agendados
    dia  // representar os dias da semana

INVARIANT       
    matriculado: MATRICULA >+> NOME  // cada matrícula tem um nome associado
    & statuspagamento: MATRICULA +-> STATUS  // o status de pagamento está associado a cada matrícula
    & historicopagamento: MATRICULA +-> 1..mes  // o histórico de pagamento está associado a cada matrícula e é um número entre 1 e o máximo de dias de um mês
    & treinando: MATRICULA +-> TREINO  // o treino em andamento está associado a cada matrícula
    & frequencia: MATRICULA --> 0..mes  // a frequência está associada a cada matrícula e é um número entre 0 e o máximo de dias de um mês
    & controlefrequencia: MATRICULA +-> FREQUENCIA  // o controle de frequência está associado a cada matrícula
    & treinos:MATRICULA*DIAS <-> serie  // os treinos agendados estão associados a cada matrícula e a cada dia da semana
    & dia <: DIAS  // o dia é um subconjunto de dias da semana
    
INITIALISATION  
    matriculado := {}  // nenhum cliente está matriculado inicialmente
    || statuspagamento := {}  // status de pagamento inicialmente é vazio
    || historicopagamento := MATRICULA*{1}  // o histórico de pagamento de cada cliente começa com dia 1
    || treinando := {}  // treino inicialmente é vazio
    || frequencia := MATRICULA*{0}  // a frequência de cada cliente começa com 0
    || controlefrequencia := MATRICULA*{false}  // o controle de frequência de cada cliente começa como falso
    || treinos:={}  // nenhum treino está agendado inicialmente
    || dia:={}  // nenhum dia da semana está definido inicialmente
    
OPERATIONS

    matricular(mm,nn) =
        PRE mm: MATRICULA  // Verifica se o número de matrícula é válido
            & nn: NOME  // Verifica se o nome é válido
            & mm /: dom(matriculado)  // Verifica se o cliente não está matriculado atualmente
            & nn /: ran(matriculado)  // Verifica se o nome não está associado a outra matrícula
        THEN matriculado(mm):=nn || statuspagamento(mm) := pago || historicopagamento(mm) := 1  // Matricula o cliente e define seu status de pagamento como pago e inicia a contagem de dias para verificar próximo pagamento
    END;
    
    checkin(mm) =
        PRE mm:MATRICULA  // Verifica se o número de matrícula é válido
            & mm/: dom(treinando)  // Verifica se o cliente não está atualmente fazendo treino
            & mm: dom(matriculado)  // Verifica se o cliente está matriculado (Lembrar de verificar duplicidade)
            & controlefrequencia(mm) = false  // Verifica se o controle de frequência do cliente está como falso
            & statuspagamento(mm) = pago  // Verifica se o cliente está com o pagamento em dia
        THEN 
            ANY tt WHERE tt:TREINO  // Seleciona um tipo de treino disponível
                THEN treinando:= treinando \/ {mm |-> tt}  // Registra que o cliente está fazendo o treino
                || frequencia(mm):= frequencia(mm)+1  // Incrementa a frequência do cliente
                || controlefrequencia(mm):=true  // Atualiza o controle de frequência para verdadeiro
        END  
    END;
    
    checkout(mm) =
        PRE mm:MATRICULA  // Verifica se o número de matrícula é válido
            & mm: dom(matriculado)  // Verifica se o cliente está matriculado
            & mm: dom(treinando)  // Verifica se o cliente está atualmente fazendo treino
            & treinando - {mm |-> treinando(mm)} : MATRICULA +-> TREINO  // Verifica se ao fazer o checkout a relação do invariante se mantém verdadeira
        THEN treinando:= treinando - {mm |-> treinando(mm)}  // Remove o cliente da lista de clientes em treinamento
    END;
    
    removerMatricula(mm) =
        PRE mm:MATRICULA  // Verifica se o número de matrícula é válido
            & mm:dom(matriculado)  // Verifica se o cliente está matriculado
            & matriculado - {mm |-> matriculado(mm)} : MATRICULA >+> NOME  // Verifica se após remoção o invariante de MATRICULADO ainda será válido
        THEN matriculado:= matriculado - {mm|->matriculado(mm)}  // Remove o cliente da lista de matriculados
            || statuspagamento:= statuspagamento - {mm |-> statuspagamento(mm)}  // Remove o status de pagamento do cliente
            || historicopagamento:=historicopagamento - {mm|->historicopagamento(mm)}  // Remove o histórico de pagamento do cliente
            || frequencia(mm) := 0  // Zera a frequência do cliente
    END;

    
    passardia =
        PRE { xx, vv | xx : dom(matriculado) & vv = historicopagamento(xx) + 1 } : MATRICULA +-> 1..30  // Verifica se é possível avançar o dia
            & { xx, ss | xx : dom(matriculado) &  ss = naopago } : MATRICULA +-> STATUS  // Verifica se é possível mudar os status de pagamento para não pago
            & { xx, vv | xx : dom(matriculado) & vv = 1 } : MATRICULA +-> 1..30  // Verifica se é o possível voltar ao dia 1 para iniciar outro mês
        THEN 
            IF #xx. (xx : dom(historicopagamento) & historicopagamento(xx)<mes )  // Verifica se o dia atual do histórico de pagamento do cliente é anterior ao final do mês
            THEN historicopagamento := historicopagamento <+ ({xx, vv | xx: dom(matriculado) & historicopagamento(xx)<mes & vv=historicopagamento(xx)+1} \/ {xx,vv | xx: dom(matriculado) & historicopagamento(xx)=mes & vv=1} )  // Atualiza o histórico de pagamento do cliente
                 || statuspagamento := statuspagamento <+ {xx,ss | xx:dom(matriculado) & historicopagamento(xx)=mes & statuspagamento(xx)/=inadimplente & ss=naopago} <+ {xx, ss | xx:dom(matriculado) & historicopagamento(xx)=mes & statuspagamento(xx)=naopago & ss=inadimplente}  // Atualiza o status de pagamento do cliente
                 || controlefrequencia := {xx, vv | xx: dom(frequencia) & vv=false}  // Define o controle de frequência como falso para todos os clientes
                 || treinando:= {}  // Remove todos os clientes da lista de clientes fazendo treino
        END
    END;

    pagar(mm) =
    PRE mm:MATRICULA  // Verifica se o número de matrícula é válido
        & mm: dom(statuspagamento)  // Verifica se o cliente está matriculado
        & statuspagamento <+ {mm |-> pago} : MATRICULA +-> STATUS  // Verifica se o status de pagamento pode ser atualizado para pago
        & statuspagamento(mm) /= pago  // Verifica se o cliente não está com o status de pagamento como pago
    THEN statuspagamento(mm):= pago || historicopagamento(mm) := 1  // Atualiza o status de pagamento do cliente para pago e inicia contagem de novo mês
    END;
    
    dd <-- queryDay(mm) =
        PRE mm:MATRICULA  // Verifica se o número de matrícula é válido
            & mm: dom(matriculado)  // Verifica se o cliente está matriculado
            & mm:dom(historicopagamento)  // Verifica se o histórico de pagamento do cliente está definido
        THEN dd:= historicopagamento(mm)  // Retorna o dia de pagamento do cliente
    END;
    
    rr <-- pagamentQuery(mm) =
        PRE mm : MATRICULA  // Verifica se o número de matrícula é válido
            & mm: dom(matriculado)  // Verifica se o cliente está matriculado
        THEN 
            IF mm : dom(statuspagamento)  // Verifica se o status de pagamento do cliente está definido
                THEN rr := statuspagamento(mm)  // Retorna o status de pagamento do cliente
        END
    END;

    addTreino(person, day, type, maxSeries, maxRep, maxWeight, unit) =
        PRE person: MATRICULA  // Verifica se o número de matrícula(person) é válido
            & day: DIAS  // Verifica se o dia é válido
            & type: TIPO  // Verifica se o tipo de treino é válido
            & maxSeries: max_series  // Verifica se o número máximo de séries é válido
            & maxRep: max_rep  // Verifica se o número máximo de repetições é válido
            & maxWeight: max_peso  // Verifica se o peso máximo é válido
            & unit: UNIDADE  // Verifica se a unidade de peso é válida
            & person: dom(matriculado)  // Verifica se o cliente está matriculado
            & (person |-> day)/: dom(treinos)  // Verifica se o cliente já tem um treino agendado para o dia especificado
        THEN treinos:= treinos \/ {(person, day) |-> [(type, maxSeries, maxRep, maxWeight, unit)]}  // Adiciona um novo treino para o cliente no dia especificado
    END;

    addExercicio(person, day, type, maxSeries, maxRep, maxWeight, unit) =
        PRE person: MATRICULA  // Verifica se o número de matrícula é válido
            & day: DIAS  // Verifica se o dia é válido
            & type: TIPO  // Verifica se o tipo de treino é válido
            & maxSeries: max_series  // Verifica se o número máximo de séries é válido
            & maxRep: max_rep  // Verifica se o número máximo de repetições é válido
            & maxWeight: max_peso  // Verifica se o peso máximo é válido
            & unit: UNIDADE  // Verifica se a unidade de peso é válida
            & matriculado(person)/: {}  // Verifica se o cliente está matriculado
            & (person |-> day): dom(treinos)  // Verifica se o cliente já tem um treino agendado para o dia especificado, caso tenha, não será possível utilizar addExercicio
        THEN treinos:= treinos \/ {(person, day) |-> [(type, maxSeries, maxRep, maxWeight, unit)]}  // Adiciona um novo exercício à lista de exercícios do cliente no dia especificado
    END;

    removerTreino(pp,dd) =
        PRE pp: MATRICULA  // Verifica se o número de matrícula é válido
            & dd: DIAS  // Verifica se o dia é válido
            & matriculado(pp)/: {}  // Verifica se o cliente está matriculado
            & (pp |-> dd) : dom(treinos)  // Verifica se o cliente tem um treino agendado para o dia especificado
        THEN treinos:=treinos-({pp|->dd} <| treinos)  // Remove o treino do cliente no dia especificado
    END;

    removerExercicio(pp,dd,ss) =
        PRE pp: MATRICULA  // Verifica se o número de matrícula é válido
            & dd:DIAS  // Verifica se o dia é válido
            & ss:serie  // Verifica se a série de exercícios é válida
            & matriculado(pp)/:{}  // Verifica se o cliente está matriculado
            & {pp|->dd|->ss} /\ treinos /= {}  // Verifica se o cliente tem um treino agendado para o dia especificado e com a série de exercícios especificada
        THEN treinos:=treinos-{pp|->dd|->ss}  // Remove a série de exercícios do treino do cliente no dia especificado
    END


END

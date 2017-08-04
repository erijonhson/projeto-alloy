/* 
 Tema 7 em https://docs.google.com/document/d/1aTb65qho0WhN38dV2OWL_4ppcrV-U2u7l6jJVrZxXwY/pub
 TODO:
 [OK] cada Professor ministra duas ou três Disciplinas de 4 horas semanais 
          ~ temos que tratar essa questão de horário? ~ 
 [    ] cada Professor pode Orientar Alunos de Graduação 
          ~ Alunos tornam-se uma assinatura (sig)? ~ 
 [    ] se Professor Doutor, então: 
         [    ] pode orientar Alunos de Mestrado ou Doutorado
                 ~ Seriam 3 tipos de Aluno, então? (Graduação, Mestrado e Doutorado)~ 
         [    ] pode ministrar aulas na pós-graduação, cumulativamente às atividades que já desenvolve 
                (estas disciplinas entram na cota mencionada acima) 
                 ~ então teremos Disciplina de Graduação e de Pós-Graduação? ~
 [    ] todos os Professores devem ter 8 atividades de alocação, cada uma de duas ou quatro horas; 
        caso contrário, o professor estará classificado como Atividade Insuficiente. 
         ~ temos que tratar essa questão de horário? ~ 
*/

module AlocacaoProfessoresDSC

--------------------------------------------------------------------------------------
--   ASSINATURAS (Mínimo 5, com ao menos 1 herança - extends ou in)
--------------------------------------------------------------------------------------
sig Professor {
	atividades : set Atividade
}

sig Atividade{}

sig Disciplina extends Atividade{}

--------------------------------------------------------------------------------------
--   FATOS 
--------------------------------------------------------------------------------------

fact ProfessorTemDuasOuTresDisciplinas {
	all p : Professor | professorComDuasOuTresDisciplinas[p]
}

fact DisciplinaTemUmProfessor {
	all a : Atividade | one a.~atividades
}

--------------------------------------------------------------------------------------
--   PREDICADOS (Mínimo 3) 
--------------------------------------------------------------------------------------

pred professorComDuasOuTresDisciplinas[p : Professor] {
	#(disciplinasDeProfessor[p]) >= 2 && #(disciplinasDeProfessor[p]) <= 3
}

--------------------------------------------------------------------------------------
--   FUNÇÕES (Mínimo 3) 
--------------------------------------------------------------------------------------

fun disciplinasDeProfessor [p : Professor]  : set Atividade {
	p.atividades & Disciplina
}

--------------------------------------------------------------------------------------
--   ASSERTS  (Mínimo 3 definições e 3 verificações) 
--------------------------------------------------------------------------------------

assert todoProfessorTemDuasOuTresDisciplinas {
    all p : Professor | #(disciplinasDeProfessor[p]) >= 2 && #(disciplinasDeProfessor[p]) <= 3
}

-- check todoProfessorTemDuasOuTresDisciplinas for 10

--------------------------------------------------------------------------------------
--   SHOW 
--------------------------------------------------------------------------------------

pred show[]{}

run show for 10

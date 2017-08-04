/* 
 Tema 7 em https://docs.google.com/document/d/1aTb65qho0WhN38dV2OWL_4ppcrV-U2u7l6jJVrZxXwY/pub
 TODO:
 [OK] cada Professor ministra duas ou três Disciplinas de 4 horas semanais 
          ~ temos que tratar essa questão de horário? ~ 
 [OK] cada Professor pode Orientar Alunos de Graduação  
 [    ] se Professor Doutor, então: 
         [OK] pode orientar Alunos de Mestrado ou Doutorado
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
abstract sig Docente {
	disciplinas : set Disciplina,
	orientandos : set Orientando
}

sig Professor extends Docente {}
sig Doutor extends Docente {}

abstract sig Disciplina {}
sig AulaDeGraduacao extends Disciplina {}
sig AulaDePosGraduacao extends Disciplina {} -- só Doutor pode 

abstract sig Orientando {}
sig Graduando extends Orientando {}
sig Mestrando extends Orientando {} -- só Doutor pode
sig Doutorando extends Orientando {} -- só Doutor pode

--------------------------------------------------------------------------------------
--   FATOS 
--------------------------------------------------------------------------------------

fact DocenteTemDuasOuTresDisciplinas {
	all d : Docente | docentesComDuasOuTresDisciplinas[d]
}

fact DisciplinaTemApenasUmProfessor {
	all d : Disciplina | one d.~disciplinas
}

fact OrientandoTemApenasUmOrientador {
	all o : Orientando | one o.~orientandos
}

fact ProfessorOrientaApenasGraduando {
	all p : Professor | professorOrientaApenasGraduando[p]
}

--------------------------------------------------------------------------------------
--   PREDICADOS (Mínimo 3) 
--------------------------------------------------------------------------------------

pred docentesComDuasOuTresDisciplinas[d : Docente] {
	#(disciplinasDeDocente[d]) >= 2 && #(disciplinasDeDocente[d]) <= 3
}

pred professorOrientaApenasGraduando[p : Professor] {
	#(mestrandosDeDocente[p]) = 0 && #(doutorandosDeDocente[p]) = 0
}

--------------------------------------------------------------------------------------
--   FUNÇÕES (Mínimo 3) 
--------------------------------------------------------------------------------------

fun disciplinasDeDocente [d : Docente]  : set Disciplina {
	d.disciplinas
}

fun mestrandosDeDocente [d : Docente]  : set Orientando {
	d.orientandos & Mestrando
}

fun doutorandosDeDocente [d : Docente]  : set Orientando {
	d.orientandos & Doutorando
}

--------------------------------------------------------------------------------------
--   ASSERTS  (Mínimo 3 definições e 3 verificações) 
--------------------------------------------------------------------------------------

assert todoProfessorTemDuasOuTresDisciplinas {
    all d : Docente | #(disciplinasDeDocente[d]) >= 2 && #(disciplinasDeDocente[d]) <= 3
}

-- check todoProfessorTemDuasOuTresDisciplinas for 10

--------------------------------------------------------------------------------------
--   SHOW 
--------------------------------------------------------------------------------------

pred show[]{}

run show for 8

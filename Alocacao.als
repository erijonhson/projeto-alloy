-- Requerimentos mínimos comuns a todos os projetos
-- Definição de 5 assinaturas, com pelo menos uma herança (extends ou in)
-- Definição de 3 predicados e 3 funções
-- Definição e verificação de 3 asserts (testes sobre o sistema)
-- Grupos: mínimo de 4, máximo de 5 integrantes por equipe.

module Professor

sig Professor {
	disciplinas : set Atividade
}

sig Atividade{}

sig Disciplina extends Atividade{}

--------------------------------------------------------------------------------------
--   FATOS    (Definindo fatos sobre o modelo)
--------------------------------------------------------------------------------------

fact ProfessorTemDuasOuTresDisciplinas {
	all p : Professor | duasOuTresDisciplinas[p]
}

fact DisciplinaTemUmProfessor {
	all a : Atividade | one a.~disciplinas
}

--------------------------------------------------------------------------------------
--   PREDICADOS (5)
--------------------------------------------------------------------------------------

pred duasOuTresDisciplinas[p : Professor] {
    #(professorComDuasOuTresDisciplinas[p]) >= 2 && #(professorComDuasOuTresDisciplinas[p]) <= 3
}

--------------------------------------------------------------------------------------
--   FUNÇÕES (1)
--------------------------------------------------------------------------------------

fun professorComDuasOuTresDisciplinas [p : Professor]  : set Atividade {
	p.disciplinas & Disciplina
}

--------------------------------------------------------------------------------------
--   ASSERTS  (1)
--------------------------------------------------------------------------------------


--------------------------------------------------------------------------------------
--   SHOW                                                                        
--------------------------------------------------------------------------------------

pred show[]{}

run show for 10

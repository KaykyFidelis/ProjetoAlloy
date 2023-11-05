//Os dois possíveis status de um perfil ou usuário
enum Status{
    inativo, ativo
}

// Bônus
// O perfil possui alguma publicação?
enum Publicou{
    TemPublicação, NaoTemPublicação
}

sig Usuario{
    statusUsuario: one Status,
    possui: some Perfil,
    podePublicar: set Perfil,
    amigos: set Usuario,
    exAmigos: set Usuario
}

sig Perfil{
    statusPerfil: one Status,
    publicacoes: one Publicou
}

fact "Restrições do Usuário" {
    // Nenhum usuário é amigo ou ex-amigo de si próprio
    all u:Usuario | u not in u.amigos and u not in u.exAmigos
    // Se um usuário é inativo, então não pode possuir relação com outros usuários
    all u:Usuario | u.statusUsuario = inativo implies (#u.amigos = 0 and #u.exAmigos = 0) 
}

fact "Restrição de Publicação" {
    // Um usuário pode publicar nos perfis de seus amigos, mas não pode publicar no de seus ex-amigos.
    all u:Usuario | (u.podePublicar = u.podePublicar + (u.amigos.possui) - (u.exAmigos.possui))
    // Se um perfil não é do usuário, nem dos amigos dele, então o usuário não pode publicar nesse perfil.
    all u:Usuario, p:Perfil | (p not in u.possui and p not in u.amigos.possui) implies p not in u.podePublicar
}

fact "Restrições do Perfil" {
    // Caso o usuário ao qual este perfil pertence esteja inativo, o mesmo deve ser inativo também
    all p:Perfil, u:Usuario | (u.statusUsuario = inativo and p in u.possui) implies p.statusPerfil = inativo
    // Caso o perfil de um usuário esteja inativo, nem ele, nem seus amigos podem publicar nele(imagine os ex-amigos hahaha, mas isso dos ex-amigos foi verificado lá em cima) 
    all p:Perfil, u:Usuario | (p in u.possui and p.statusPerfil = inativo) implies (p not in u.podePublicar and p not in u.amigos.podePublicar)
    // Cada perfil possui apenas um único usuário que o possui(note que não existem perfis que não pertencem à nenhum usuário)
    all p: Perfil | one u: Usuario | p in u.possui
    // Se o perfil está inativo, não possui publicações
    all p:Perfil | p.statusPerfil = inativo implies p.publicacoes = NaoTemPublicação
}

fact "Restrição de Amizade" {
    // Um usuário não pode ser amigo e ex-amigo ao mesmo tempo de outro usuário
    all u1, u2: Usuario | not (u1 in u2.amigos and u1 in u2.exAmigos) and not (u2 in u1.amigos and u2 in u1.exAmigos)
    // A relação de amizade e inimizade deve ser mútua
    all u1, u2: Usuario | (u1 in u2.amigos <=> u2 in u1.amigos) and (u1 in u2.exAmigos <=> u2 in u1.exAmigos)
}

// Não existe um amigo e um exAmigo ao mesmo tempo
assert amigos {
    all u1,u2:Usuario | not ((u1 in u2.amigos) and (u1 in u2.exAmigos))
}
check amigos

assert ativoPublicaInativo {
    all u1,u2:Usuario | all p1:u1.podePublicar | ((u1 in u2.amigos) and (inativo in u2.statusUsuario)) implies (not p1 in u2.possui)
}
check ativoPublicaInativo

assert UsuarioInativoAndPerfilInativo {
    all u:Usuario | all p:u.possui | (inativo in u.statusUsuario) implies (inativo in p.statusPerfil)
}
check UsuarioInativoAndPerfilInativo

assert atLeastOnePerfil {
    all u:Usuario | #(u.possui) > 0
}
check atLeastOnePerfil

assert belongsToOnlyOneUser {
    all u1,u2:Usuario | (u1 != u2) implies (all p:u1.possui | (not p in u2.possui))
}
check belongsToOnlyOneUser

assert mutuals {
    all u1, u2: Usuario | (u1 in u2.amigos implies u2 in u1.amigos) and (u2 in u1.amigos implies u1 in u2.amigos)
    all u1, u2: Usuario | (u1 in u2.exAmigos implies u2 in u1.exAmigos) and (u2 in u1.exAmigos implies u1 in u2.exAmigos)
}
check mutuals

assert ownFriend {
    all u:Usuario | not (u in u.amigos || u in u.exAmigos)
}
check ownFriend

assert postPerfilInativo {
    all u:Usuario | all p:u.possui | (inativo in u.statusUsuario) implies (NaoTemPublicação in p.publicacoes)
}
check postPerfilInativo

assert UsuarioInativoNoFriends {
    all u:Usuario | inativo in u.statusUsuario implies (#(u.amigos) = 0 and #(u.exAmigos) = 0)
}
check UsuarioInativoNoFriends

run {} 

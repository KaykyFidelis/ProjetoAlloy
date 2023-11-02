/*
A plataforma de mídia social deve suportar perfis de usuário, conexões de amizade e 
publicação de conteúdo de texto. As seguintes restrições devem ser seguidas:

1. Um usuário pode ter mais de um perfil. Perfis e usuários podem estar ativos ou inativos.
2. Conexões de amizade entre os usuários devem ser estabelecidas. 
3. O sistema deve ter um histórico das conexões atuais e apagadas.
4. Um usuário pode publicar conteúdo de texto em seu perfil ou nos perfis de seus amigos.
- A especificação Alloy deve representar esses recursos e capturar as relações entre usuários, amizades e postagens. 

- Além disso, devem existir restrições para garantir que o modelo seja bem definido e satisfaça certas propriedades 
(por exemplo, os usuários não podem ser amigos de si mesmos, as postagens devem 
estar associadas a usuários ativos, etc.).
*/

sig Usuario{
    ativo: lone Status,
    inativo: lone Status,
    perfis: set Perfil
}

sig Perfil{}

one sig Status{}

fact "Restrições do Usuário"{
    
}

run{}

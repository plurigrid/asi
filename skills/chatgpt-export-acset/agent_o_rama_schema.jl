# Auto-generated from ChatGPT export
using ACSets

@present SchChatGPT(FreeSchema) begin
    Conversation::Ob
    Message::Ob
    Author::Ob
    
    conversation_of::Hom(Message, Conversation)
    author_of::Hom(Message, Author)
    parent_msg::Hom(Message, Message)
    
    Title::AttrType
    Content::AttrType
    Role::AttrType
    Time::AttrType
    
    title::Attr(Conversation, Title)
    content::Attr(Message, Content)
    role::Attr(Author, Role)
end

# Data extracted: 39 conversations, 2798 messages

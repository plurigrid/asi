#!/usr/bin/env python3
import os, json, struct

MAJOR = ["The Fool","The Magician","The High Priestess","The Empress","The Emperor",
"The Hierophant","The Lovers","The Chariot","Strength","The Hermit",
"Wheel of Fortune","Justice","The Hanged Man","Death","Temperance",
"The Devil","The Tower","The Star","The Moon","The Sun","Judgement","The World"]
SUITS = ["wands","cups","swords","pentacles"]
RANKS = ["Ace","Two","Three","Four","Five","Six","Seven","Eight","Nine","Ten","Page","Knight","Queen","King"]

def secure_randint(n):
    k = (n-1).bit_length()
    mask = (1 << k) - 1
    while True:
        val = struct.unpack("I", os.urandom(4))[0] & mask
        if val < n: return val

def build_deck():
    deck = []
    for name in MAJOR:
        slug = name.lower().replace(" ","-").replace("the-","")
        deck.append({"name":name,"file":f"cards/major/{slug}.md","arcana":"major"})
    for suit in SUITS:
        for rank in RANKS:
            slug = f"{rank.lower()}-of-{suit}"
            deck.append({"name":f"{rank} of {suit.title()}","file":f"cards/{suit}/{slug}.md","arcana":"minor"})
    return deck

def draw(n=4):
    deck = build_deck()
    for i in range(len(deck)-1, 0, -1):
        j = secure_randint(i+1)
        deck[i], deck[j] = deck[j], deck[i]
    positions = ["The Context","The Challenge","The Guidance","The Outcome"]
    return [dict(deck[i], position=positions[i], reversed=secure_randint(2)==1) for i in range(n)]

if __name__ == "__main__":
    print(json.dumps(draw(), indent=2))

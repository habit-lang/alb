requires qprelude

type HWord = Bit 16
type Word = Bit 32

primitive (:#) :: Bit m -> Bit n -> Bit (m + n)

padHigh :: HWord -> Word
padHigh low = 0 :# low

padLow :: HWord -> Word
padLow high = high :# 0

data Foo = Foo HWord HWord

build :: Foo -> Word
build (Foo high low) = high :# low

getHigh (Foo high _) = high
getLow (Foo _ low) = low

getHigh' :: Foo -> HWord
getHigh' (Foo high _) = high

bitdata FooB = FooB [ low = 0, high :: HWord ]

buildb :: FooB -> Word
buildb (FooB r) = r.high :# r.low

getHighb (FooB r) = r.high
getLowb (FooB r) = r.low

getHighb' :: FooB -> HWord
getHighb' (FooB r) = r.high

struct FooS [ low <- 0, high :: Stored HWord ]

getHighS r = readRef (r.low)

getHighS' :: Ref FooS -> M HWord
getHighS' r = readRef (r.low)
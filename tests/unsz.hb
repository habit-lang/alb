requires miniprelude

primitive (:#) :: Bit m -> Bit n -> Bit (m + n)

unsz :: n < 33 => Bit n -> Bit 32
unsz x = 0 :# x

main () = unsz (1 :: Bit 15)
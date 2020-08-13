structure MyStruct =
  let
    open Int String
  in
    MyFunctor (
      struct
        val f = +
      end
    )
  end

def divps1 : instruction :=
  definst "divps" $ do
    pattern fun (v_2825 : reg (bv 128)) (v_2826 : reg (bv 128)) => do
      v_4563 <- getRegister v_2826;
      v_4566 <- getRegister v_2825;
      setRegister (lhs.of_reg v_2826) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_4563 0 32) 24 8) (MInt2Float (extract v_4566 0 32) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_4563 32 64) 24 8) (MInt2Float (extract v_4566 32 64) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_4563 64 96) 24 8) (MInt2Float (extract v_4566 64 96) 24 8)) 32) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_4563 96 128) 24 8) (MInt2Float (extract v_4566 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2821 : Mem) (v_2822 : reg (bv 128)) => do
      v_8079 <- getRegister v_2822;
      v_8082 <- evaluateAddress v_2821;
      v_8083 <- load v_8082 16;
      setRegister (lhs.of_reg v_2822) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_8079 0 32) 24 8) (MInt2Float (extract v_8083 0 32) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_8079 32 64) 24 8) (MInt2Float (extract v_8083 32 64) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_8079 64 96) 24 8) (MInt2Float (extract v_8083 64 96) 24 8)) 32) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_8079 96 128) 24 8) (MInt2Float (extract v_8083 96 128) 24 8)) 32))));
      pure ()
    pat_end

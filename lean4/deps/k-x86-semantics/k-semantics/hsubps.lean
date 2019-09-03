def hsubps1 : instruction :=
  definst "hsubps" $ do
    pattern fun (v_2841 : reg (bv 128)) (v_2842 : reg (bv 128)) => do
      v_4865 <- getRegister v_2841;
      v_4879 <- getRegister v_2842;
      setRegister (lhs.of_reg v_2842) (concat (concat (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4865 32 64) 24 8) (MInt2Float (extract v_4865 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4865 96 128) 24 8) (MInt2Float (extract v_4865 64 96) 24 8)) 32)) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4879 32 64) 24 8) (MInt2Float (extract v_4879 0 32) 24 8)) 32)) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4879 96 128) 24 8) (MInt2Float (extract v_4879 64 96) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2837 : Mem) (v_2838 : reg (bv 128)) => do
      v_8548 <- evaluateAddress v_2837;
      v_8549 <- load v_8548 16;
      v_8563 <- getRegister v_2838;
      setRegister (lhs.of_reg v_2838) (concat (concat (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_8549 32 64) 24 8) (MInt2Float (extract v_8549 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_8549 96 128) 24 8) (MInt2Float (extract v_8549 64 96) 24 8)) 32)) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_8563 32 64) 24 8) (MInt2Float (extract v_8563 0 32) 24 8)) 32)) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_8563 96 128) 24 8) (MInt2Float (extract v_8563 64 96) 24 8)) 32));
      pure ()
    pat_end

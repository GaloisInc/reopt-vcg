def hsubps1 : instruction :=
  definst "hsubps" $ do
    pattern fun (v_2906 : reg (bv 128)) (v_2907 : reg (bv 128)) => do
      v_4842 <- getRegister v_2906;
      v_4856 <- getRegister v_2907;
      setRegister (lhs.of_reg v_2907) (concat (concat (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4842 32 64) 24 8) (MInt2Float (extract v_4842 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4842 96 128) 24 8) (MInt2Float (extract v_4842 64 96) 24 8)) 32)) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4856 32 64) 24 8) (MInt2Float (extract v_4856 0 32) 24 8)) 32)) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4856 96 128) 24 8) (MInt2Float (extract v_4856 64 96) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2901 : Mem) (v_2902 : reg (bv 128)) => do
      v_8314 <- evaluateAddress v_2901;
      v_8315 <- load v_8314 16;
      v_8329 <- getRegister v_2902;
      setRegister (lhs.of_reg v_2902) (concat (concat (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_8315 32 64) 24 8) (MInt2Float (extract v_8315 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_8315 96 128) 24 8) (MInt2Float (extract v_8315 64 96) 24 8)) 32)) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_8329 32 64) 24 8) (MInt2Float (extract v_8329 0 32) 24 8)) 32)) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_8329 96 128) 24 8) (MInt2Float (extract v_8329 64 96) 24 8)) 32));
      pure ()
    pat_end

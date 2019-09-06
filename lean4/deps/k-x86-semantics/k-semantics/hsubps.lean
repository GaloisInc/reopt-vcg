def hsubps1 : instruction :=
  definst "hsubps" $ do
    pattern fun (v_2932 : reg (bv 128)) (v_2933 : reg (bv 128)) => do
      v_4863 <- getRegister v_2932;
      v_4877 <- getRegister v_2933;
      setRegister (lhs.of_reg v_2933) (concat (concat (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4863 32 64) 24 8) (MInt2Float (extract v_4863 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4863 96 128) 24 8) (MInt2Float (extract v_4863 64 96) 24 8)) 32)) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4877 32 64) 24 8) (MInt2Float (extract v_4877 0 32) 24 8)) 32)) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4877 96 128) 24 8) (MInt2Float (extract v_4877 64 96) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2928 : Mem) (v_2929 : reg (bv 128)) => do
      v_8324 <- evaluateAddress v_2928;
      v_8325 <- load v_8324 16;
      v_8339 <- getRegister v_2929;
      setRegister (lhs.of_reg v_2929) (concat (concat (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_8325 32 64) 24 8) (MInt2Float (extract v_8325 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_8325 96 128) 24 8) (MInt2Float (extract v_8325 64 96) 24 8)) 32)) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_8339 32 64) 24 8) (MInt2Float (extract v_8339 0 32) 24 8)) 32)) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_8339 96 128) 24 8) (MInt2Float (extract v_8339 64 96) 24 8)) 32));
      pure ()
    pat_end

def addsubps1 : instruction :=
  definst "addsubps" $ do
    pattern fun (v_2732 : reg (bv 128)) (v_2733 : reg (bv 128)) => do
      v_4950 <- getRegister v_2733;
      v_4953 <- getRegister v_2732;
      setRegister (lhs.of_reg v_2733) (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4950 0 32) 24 8) (MInt2Float (extract v_4953 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4950 32 64) 24 8) (MInt2Float (extract v_4953 32 64) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4950 64 96) 24 8) (MInt2Float (extract v_4953 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4950 96 128) 24 8) (MInt2Float (extract v_4953 96 128) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_2727 : Mem) (v_2728 : reg (bv 128)) => do
      v_9035 <- getRegister v_2728;
      v_9038 <- evaluateAddress v_2727;
      v_9039 <- load v_9038 16;
      setRegister (lhs.of_reg v_2728) (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9035 0 32) 24 8) (MInt2Float (extract v_9039 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9035 32 64) 24 8) (MInt2Float (extract v_9039 32 64) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9035 64 96) 24 8) (MInt2Float (extract v_9039 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9035 96 128) 24 8) (MInt2Float (extract v_9039 96 128) 24 8)) 32)));
      pure ()
    pat_end

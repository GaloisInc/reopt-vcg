def vcvtdq2pd1 : instruction :=
  definst "vcvtdq2pd" $ do
    pattern fun (v_3093 : reg (bv 128)) (v_3094 : reg (bv 128)) => do
      v_5739 <- getRegister v_3093;
      setRegister (lhs.of_reg v_3094) (concat (Float2MInt (Int2Float (svalueMInt (extract v_5739 64 96)) 53 11) 64) (Float2MInt (Int2Float (svalueMInt (extract v_5739 96 128)) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (v_3099 : reg (bv 256)) (v_3100 : reg (bv 256)) => do
      v_5754 <- getRegister v_3099;
      setRegister (lhs.of_reg v_3100) (concat (Float2MInt (Int2Float (svalueMInt (extract v_5754 128 160)) 53 11) 64) (concat (Float2MInt (Int2Float (svalueMInt (extract v_5754 160 192)) 53 11) 64) (concat (Float2MInt (Int2Float (svalueMInt (extract v_5754 192 224)) 53 11) 64) (Float2MInt (Int2Float (svalueMInt (extract v_5754 224 256)) 53 11) 64))));
      pure ()
    pat_end;
    pattern fun (v_3086 : Mem) (v_3089 : reg (bv 128)) => do
      v_9883 <- evaluateAddress v_3086;
      v_9884 <- load v_9883 8;
      setRegister (lhs.of_reg v_3089) (concat (Float2MInt (Int2Float (svalueMInt (extract v_9884 0 32)) 53 11) 64) (Float2MInt (Int2Float (svalueMInt (extract v_9884 32 64)) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (v_3095 : Mem) (v_3096 : reg (bv 256)) => do
      v_9895 <- evaluateAddress v_3095;
      v_9896 <- load v_9895 16;
      setRegister (lhs.of_reg v_3096) (concat (Float2MInt (Int2Float (svalueMInt (extract v_9896 0 32)) 53 11) 64) (concat (Float2MInt (Int2Float (svalueMInt (extract v_9896 32 64)) 53 11) 64) (concat (Float2MInt (Int2Float (svalueMInt (extract v_9896 64 96)) 53 11) 64) (Float2MInt (Int2Float (svalueMInt (extract v_9896 96 128)) 53 11) 64))));
      pure ()
    pat_end

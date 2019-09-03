def vcvtdq2pd1 : instruction :=
  definst "vcvtdq2pd" $ do
    pattern fun (v_3015 : reg (bv 128)) (v_3016 : reg (bv 128)) => do
      v_6249 <- getRegister v_3015;
      setRegister (lhs.of_reg v_3016) (concat (Float2MInt (Int2Float (svalueMInt (extract v_6249 64 96)) 53 11) 64) (Float2MInt (Int2Float (svalueMInt (extract v_6249 96 128)) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (v_3021 : reg (bv 256)) (v_3022 : reg (bv 256)) => do
      v_6264 <- getRegister v_3021;
      setRegister (lhs.of_reg v_3022) (concat (Float2MInt (Int2Float (svalueMInt (extract v_6264 128 160)) 53 11) 64) (concat (Float2MInt (Int2Float (svalueMInt (extract v_6264 160 192)) 53 11) 64) (concat (Float2MInt (Int2Float (svalueMInt (extract v_6264 192 224)) 53 11) 64) (Float2MInt (Int2Float (svalueMInt (extract v_6264 224 256)) 53 11) 64))));
      pure ()
    pat_end;
    pattern fun (v_3008 : Mem) (v_3011 : reg (bv 128)) => do
      v_11636 <- evaluateAddress v_3008;
      v_11637 <- load v_11636 8;
      setRegister (lhs.of_reg v_3011) (concat (Float2MInt (Int2Float (svalueMInt (extract v_11637 0 32)) 53 11) 64) (Float2MInt (Int2Float (svalueMInt (extract v_11637 32 64)) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (v_3017 : Mem) (v_3018 : reg (bv 256)) => do
      v_11648 <- evaluateAddress v_3017;
      v_11649 <- load v_11648 16;
      setRegister (lhs.of_reg v_3018) (concat (Float2MInt (Int2Float (svalueMInt (extract v_11649 0 32)) 53 11) 64) (concat (Float2MInt (Int2Float (svalueMInt (extract v_11649 32 64)) 53 11) 64) (concat (Float2MInt (Int2Float (svalueMInt (extract v_11649 64 96)) 53 11) 64) (Float2MInt (Int2Float (svalueMInt (extract v_11649 96 128)) 53 11) 64))));
      pure ()
    pat_end

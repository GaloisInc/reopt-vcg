def vcvtdq2pd1 : instruction :=
  definst "vcvtdq2pd" $ do
    pattern fun (v_3066 : reg (bv 128)) (v_3067 : reg (bv 128)) => do
      v_5712 <- getRegister v_3066;
      setRegister (lhs.of_reg v_3067) (concat (Float2MInt (Int2Float (svalueMInt (extract v_5712 64 96)) 53 11) 64) (Float2MInt (Int2Float (svalueMInt (extract v_5712 96 128)) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (v_3074 : reg (bv 256)) (v_3075 : reg (bv 256)) => do
      v_5727 <- getRegister v_3074;
      setRegister (lhs.of_reg v_3075) (concat (Float2MInt (Int2Float (svalueMInt (extract v_5727 128 160)) 53 11) 64) (concat (Float2MInt (Int2Float (svalueMInt (extract v_5727 160 192)) 53 11) 64) (concat (Float2MInt (Int2Float (svalueMInt (extract v_5727 192 224)) 53 11) 64) (Float2MInt (Int2Float (svalueMInt (extract v_5727 224 256)) 53 11) 64))));
      pure ()
    pat_end;
    pattern fun (v_3061 : Mem) (v_3062 : reg (bv 128)) => do
      v_9856 <- evaluateAddress v_3061;
      v_9857 <- load v_9856 8;
      setRegister (lhs.of_reg v_3062) (concat (Float2MInt (Int2Float (svalueMInt (extract v_9857 0 32)) 53 11) 64) (Float2MInt (Int2Float (svalueMInt (extract v_9857 32 64)) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (v_3070 : Mem) (v_3071 : reg (bv 256)) => do
      v_9868 <- evaluateAddress v_3070;
      v_9869 <- load v_9868 16;
      setRegister (lhs.of_reg v_3071) (concat (Float2MInt (Int2Float (svalueMInt (extract v_9869 0 32)) 53 11) 64) (concat (Float2MInt (Int2Float (svalueMInt (extract v_9869 32 64)) 53 11) 64) (concat (Float2MInt (Int2Float (svalueMInt (extract v_9869 64 96)) 53 11) 64) (Float2MInt (Int2Float (svalueMInt (extract v_9869 96 128)) 53 11) 64))));
      pure ()
    pat_end

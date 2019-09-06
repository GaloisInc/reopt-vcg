def vcvtps2ph1 : instruction :=
  definst "vcvtps2ph" $ do
    pattern fun (v_3218 : imm int) (v_3222 : reg (bv 128)) (v_3223 : reg (bv 128)) => do
      v_6077 <- getRegister v_3222;
      v_6081 <- eval (uvalueMInt (handleImmediateWithSignExtend v_3218 8 8));
      setRegister (lhs.of_reg v_3223) (concat (expression.bv_nat 64 0) (concat (Float2MInt (Float2Half (MInt2Float (extract v_6077 0 32) 24 8) v_6081) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_6077 32 64) 24 8) v_6081) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_6077 64 96) 24 8) v_6081) 16) (Float2MInt (Float2Half (MInt2Float (extract v_6077 96 128) 24 8) v_6081) 16)))));
      pure ()
    pat_end;
    pattern fun (v_3224 : imm int) (v_3225 : reg (bv 256)) (v_3229 : reg (bv 128)) => do
      v_6101 <- getRegister v_3225;
      v_6105 <- eval (uvalueMInt (handleImmediateWithSignExtend v_3224 8 8));
      setRegister (lhs.of_reg v_3229) (concat (Float2MInt (Float2Half (MInt2Float (extract v_6101 0 32) 24 8) v_6105) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_6101 32 64) 24 8) v_6105) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_6101 64 96) 24 8) v_6105) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_6101 96 128) 24 8) v_6105) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_6101 128 160) 24 8) v_6105) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_6101 160 192) 24 8) v_6105) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_6101 192 224) 24 8) v_6105) 16) (Float2MInt (Float2Half (MInt2Float (extract v_6101 224 256) 24 8) v_6105) 16))))))));
      pure ()
    pat_end;
    pattern fun (v_3208 : imm int) (v_3210 : reg (bv 256)) (v_3209 : Mem) => do
      v_10746 <- evaluateAddress v_3209;
      v_10747 <- getRegister v_3210;
      v_10751 <- eval (uvalueMInt (handleImmediateWithSignExtend v_3208 8 8));
      store v_10746 (concat (Float2MInt (Float2Half (MInt2Float (extract v_10747 0 32) 24 8) v_10751) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_10747 32 64) 24 8) v_10751) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_10747 64 96) 24 8) v_10751) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_10747 96 128) 24 8) v_10751) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_10747 128 160) 24 8) v_10751) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_10747 160 192) 24 8) v_10751) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_10747 192 224) 24 8) v_10751) 16) (Float2MInt (Float2Half (MInt2Float (extract v_10747 224 256) 24 8) v_10751) 16)))))))) 16;
      pure ()
    pat_end;
    pattern fun (v_3213 : imm int) (v_3217 : reg (bv 128)) (v_3214 : Mem) => do
      v_10790 <- evaluateAddress v_3214;
      v_10791 <- getRegister v_3217;
      v_10795 <- eval (uvalueMInt (handleImmediateWithSignExtend v_3213 8 8));
      store v_10790 (concat (Float2MInt (Float2Half (MInt2Float (extract v_10791 0 32) 24 8) v_10795) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_10791 32 64) 24 8) v_10795) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_10791 64 96) 24 8) v_10795) 16) (Float2MInt (Float2Half (MInt2Float (extract v_10791 96 128) 24 8) v_10795) 16)))) 8;
      pure ()
    pat_end

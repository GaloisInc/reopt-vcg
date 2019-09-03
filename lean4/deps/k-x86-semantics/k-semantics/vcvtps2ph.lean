def vcvtps2ph1 : instruction :=
  definst "vcvtps2ph" $ do
    pattern fun (v_3127 : imm int) (v_3131 : reg (bv 128)) (v_3132 : reg (bv 128)) => do
      v_6128 <- getRegister v_3131;
      v_6132 <- eval (uvalueMInt (handleImmediateWithSignExtend v_3127 8 8));
      setRegister (lhs.of_reg v_3132) (concat (expression.bv_nat 64 0) (concat (Float2MInt (Float2Half (MInt2Float (extract v_6128 0 32) 24 8) v_6132) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_6128 32 64) 24 8) v_6132) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_6128 64 96) 24 8) v_6132) 16) (Float2MInt (Float2Half (MInt2Float (extract v_6128 96 128) 24 8) v_6132) 16)))));
      pure ()
    pat_end;
    pattern fun (v_3133 : imm int) (v_3135 : reg (bv 256)) (v_3138 : reg (bv 128)) => do
      v_6152 <- getRegister v_3135;
      v_6156 <- eval (uvalueMInt (handleImmediateWithSignExtend v_3133 8 8));
      setRegister (lhs.of_reg v_3138) (concat (Float2MInt (Float2Half (MInt2Float (extract v_6152 0 32) 24 8) v_6156) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_6152 32 64) 24 8) v_6156) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_6152 64 96) 24 8) v_6156) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_6152 96 128) 24 8) v_6156) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_6152 128 160) 24 8) v_6156) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_6152 160 192) 24 8) v_6156) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_6152 192 224) 24 8) v_6156) 16) (Float2MInt (Float2Half (MInt2Float (extract v_6152 224 256) 24 8) v_6156) 16))))))));
      pure ()
    pat_end;
    pattern fun (v_3118 : imm int) (v_3119 : reg (bv 256)) (v_3117 : Mem) => do
      v_10977 <- evaluateAddress v_3117;
      v_10978 <- getRegister v_3119;
      v_10982 <- eval (uvalueMInt (handleImmediateWithSignExtend v_3118 8 8));
      store v_10977 (concat (Float2MInt (Float2Half (MInt2Float (extract v_10978 0 32) 24 8) v_10982) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_10978 32 64) 24 8) v_10982) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_10978 64 96) 24 8) v_10982) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_10978 96 128) 24 8) v_10982) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_10978 128 160) 24 8) v_10982) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_10978 160 192) 24 8) v_10982) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_10978 192 224) 24 8) v_10982) 16) (Float2MInt (Float2Half (MInt2Float (extract v_10978 224 256) 24 8) v_10982) 16)))))))) 16;
      pure ()
    pat_end;
    pattern fun (v_3123 : imm int) (v_3126 : reg (bv 128)) (v_3122 : Mem) => do
      v_11021 <- evaluateAddress v_3122;
      v_11022 <- getRegister v_3126;
      v_11026 <- eval (uvalueMInt (handleImmediateWithSignExtend v_3123 8 8));
      store v_11021 (concat (Float2MInt (Float2Half (MInt2Float (extract v_11022 0 32) 24 8) v_11026) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_11022 32 64) 24 8) v_11026) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_11022 64 96) 24 8) v_11026) 16) (Float2MInt (Float2Half (MInt2Float (extract v_11022 96 128) 24 8) v_11026) 16)))) 8;
      pure ()
    pat_end

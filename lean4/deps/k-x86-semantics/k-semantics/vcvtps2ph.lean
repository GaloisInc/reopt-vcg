def vcvtps2ph1 : instruction :=
  definst "vcvtps2ph" $ do
    pattern fun (v_3193 : imm int) (v_3195 : reg (bv 128)) (v_3196 : reg (bv 128)) => do
      v_6050 <- getRegister v_3195;
      v_6054 <- eval (uvalueMInt (handleImmediateWithSignExtend v_3193 8 8));
      setRegister (lhs.of_reg v_3196) (concat (expression.bv_nat 64 0) (concat (Float2MInt (Float2Half (MInt2Float (extract v_6050 0 32) 24 8) v_6054) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_6050 32 64) 24 8) v_6054) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_6050 64 96) 24 8) v_6054) 16) (Float2MInt (Float2Half (MInt2Float (extract v_6050 96 128) 24 8) v_6054) 16)))));
      pure ()
    pat_end;
    pattern fun (v_3199 : imm int) (v_3200 : reg (bv 256)) (v_3202 : reg (bv 128)) => do
      v_6074 <- getRegister v_3200;
      v_6078 <- eval (uvalueMInt (handleImmediateWithSignExtend v_3199 8 8));
      setRegister (lhs.of_reg v_3202) (concat (Float2MInt (Float2Half (MInt2Float (extract v_6074 0 32) 24 8) v_6078) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_6074 32 64) 24 8) v_6078) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_6074 64 96) 24 8) v_6078) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_6074 96 128) 24 8) v_6078) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_6074 128 160) 24 8) v_6078) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_6074 160 192) 24 8) v_6078) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_6074 192 224) 24 8) v_6078) 16) (Float2MInt (Float2Half (MInt2Float (extract v_6074 224 256) 24 8) v_6078) 16))))))));
      pure ()
    pat_end;
    pattern fun (v_3183 : imm int) (v_3185 : reg (bv 256)) (v_3184 : Mem) => do
      v_10719 <- evaluateAddress v_3184;
      v_10720 <- getRegister v_3185;
      v_10724 <- eval (uvalueMInt (handleImmediateWithSignExtend v_3183 8 8));
      store v_10719 (concat (Float2MInt (Float2Half (MInt2Float (extract v_10720 0 32) 24 8) v_10724) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_10720 32 64) 24 8) v_10724) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_10720 64 96) 24 8) v_10724) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_10720 96 128) 24 8) v_10724) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_10720 128 160) 24 8) v_10724) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_10720 160 192) 24 8) v_10724) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_10720 192 224) 24 8) v_10724) 16) (Float2MInt (Float2Half (MInt2Float (extract v_10720 224 256) 24 8) v_10724) 16)))))))) 16;
      pure ()
    pat_end;
    pattern fun (v_3188 : imm int) (v_3190 : reg (bv 128)) (v_3189 : Mem) => do
      v_10763 <- evaluateAddress v_3189;
      v_10764 <- getRegister v_3190;
      v_10768 <- eval (uvalueMInt (handleImmediateWithSignExtend v_3188 8 8));
      store v_10763 (concat (Float2MInt (Float2Half (MInt2Float (extract v_10764 0 32) 24 8) v_10768) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_10764 32 64) 24 8) v_10768) 16) (concat (Float2MInt (Float2Half (MInt2Float (extract v_10764 64 96) 24 8) v_10768) 16) (Float2MInt (Float2Half (MInt2Float (extract v_10764 96 128) 24 8) v_10768) 16)))) 8;
      pure ()
    pat_end

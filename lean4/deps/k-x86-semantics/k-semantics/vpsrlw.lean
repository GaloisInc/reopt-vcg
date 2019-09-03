def vpsrlw1 : instruction :=
  definst "vpsrlw" $ do
    pattern fun (v_3417 : imm int) (v_3419 : reg (bv 128)) (v_3420 : reg (bv 128)) => do
      v_9067 <- eval (handleImmediateWithSignExtend v_3417 8 8);
      v_9070 <- getRegister v_3419;
      v_9073 <- eval (uvalueMInt (concat (expression.bv_nat 8 0) v_9067));
      setRegister (lhs.of_reg v_3420) (mux (ugt (concat (expression.bv_nat 56 0) v_9067) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (lshr (extract v_9070 0 16) v_9073) (concat (lshr (extract v_9070 16 32) v_9073) (concat (lshr (extract v_9070 32 48) v_9073) (concat (lshr (extract v_9070 48 64) v_9073) (concat (lshr (extract v_9070 64 80) v_9073) (concat (lshr (extract v_9070 80 96) v_9073) (concat (lshr (extract v_9070 96 112) v_9073) (lshr (extract v_9070 112 128) v_9073)))))))));
      pure ()
    pat_end;
    pattern fun (v_3429 : reg (bv 128)) (v_3430 : reg (bv 128)) (v_3431 : reg (bv 128)) => do
      v_9103 <- getRegister v_3429;
      v_9106 <- getRegister v_3430;
      v_9109 <- eval (uvalueMInt (extract v_9103 112 128));
      setRegister (lhs.of_reg v_3431) (mux (ugt (extract v_9103 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (lshr (extract v_9106 0 16) v_9109) (concat (lshr (extract v_9106 16 32) v_9109) (concat (lshr (extract v_9106 32 48) v_9109) (concat (lshr (extract v_9106 48 64) v_9109) (concat (lshr (extract v_9106 64 80) v_9109) (concat (lshr (extract v_9106 80 96) v_9109) (concat (lshr (extract v_9106 96 112) v_9109) (lshr (extract v_9106 112 128) v_9109)))))))));
      pure ()
    pat_end;
    pattern fun (v_3434 : imm int) (v_3437 : reg (bv 256)) (v_3438 : reg (bv 256)) => do
      v_9134 <- eval (handleImmediateWithSignExtend v_3434 8 8);
      v_9137 <- getRegister v_3437;
      v_9140 <- eval (uvalueMInt (concat (expression.bv_nat 8 0) v_9134));
      setRegister (lhs.of_reg v_3438) (mux (ugt (concat (expression.bv_nat 56 0) v_9134) (expression.bv_nat 64 15)) (expression.bv_nat 256 0) (concat (lshr (extract v_9137 0 16) v_9140) (concat (lshr (extract v_9137 16 32) v_9140) (concat (lshr (extract v_9137 32 48) v_9140) (concat (lshr (extract v_9137 48 64) v_9140) (concat (lshr (extract v_9137 64 80) v_9140) (concat (lshr (extract v_9137 80 96) v_9140) (concat (lshr (extract v_9137 96 112) v_9140) (concat (lshr (extract v_9137 112 128) v_9140) (concat (lshr (extract v_9137 128 144) v_9140) (concat (lshr (extract v_9137 144 160) v_9140) (concat (lshr (extract v_9137 160 176) v_9140) (concat (lshr (extract v_9137 176 192) v_9140) (concat (lshr (extract v_9137 192 208) v_9140) (concat (lshr (extract v_9137 208 224) v_9140) (concat (lshr (extract v_9137 224 240) v_9140) (lshr (extract v_9137 240 256) v_9140)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3446 : reg (bv 128)) (v_3448 : reg (bv 256)) (v_3449 : reg (bv 256)) => do
      v_9194 <- getRegister v_3446;
      v_9197 <- getRegister v_3448;
      v_9200 <- eval (uvalueMInt (extract v_9194 112 128));
      setRegister (lhs.of_reg v_3449) (mux (ugt (extract v_9194 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 256 0) (concat (lshr (extract v_9197 0 16) v_9200) (concat (lshr (extract v_9197 16 32) v_9200) (concat (lshr (extract v_9197 32 48) v_9200) (concat (lshr (extract v_9197 48 64) v_9200) (concat (lshr (extract v_9197 64 80) v_9200) (concat (lshr (extract v_9197 80 96) v_9200) (concat (lshr (extract v_9197 96 112) v_9200) (concat (lshr (extract v_9197 112 128) v_9200) (concat (lshr (extract v_9197 128 144) v_9200) (concat (lshr (extract v_9197 144 160) v_9200) (concat (lshr (extract v_9197 160 176) v_9200) (concat (lshr (extract v_9197 176 192) v_9200) (concat (lshr (extract v_9197 192 208) v_9200) (concat (lshr (extract v_9197 208 224) v_9200) (concat (lshr (extract v_9197 224 240) v_9200) (lshr (extract v_9197 240 256) v_9200)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3423 : Mem) (v_3424 : reg (bv 128)) (v_3425 : reg (bv 128)) => do
      v_14955 <- evaluateAddress v_3423;
      v_14956 <- load v_14955 16;
      v_14959 <- getRegister v_3424;
      v_14962 <- eval (uvalueMInt (extract v_14956 112 128));
      setRegister (lhs.of_reg v_3425) (mux (ugt (extract v_14956 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (lshr (extract v_14959 0 16) v_14962) (concat (lshr (extract v_14959 16 32) v_14962) (concat (lshr (extract v_14959 32 48) v_14962) (concat (lshr (extract v_14959 48 64) v_14962) (concat (lshr (extract v_14959 64 80) v_14962) (concat (lshr (extract v_14959 80 96) v_14962) (concat (lshr (extract v_14959 96 112) v_14962) (lshr (extract v_14959 112 128) v_14962)))))))));
      pure ()
    pat_end;
    pattern fun (v_3440 : Mem) (v_3442 : reg (bv 256)) (v_3443 : reg (bv 256)) => do
      v_14987 <- evaluateAddress v_3440;
      v_14988 <- load v_14987 16;
      v_14991 <- getRegister v_3442;
      v_14994 <- eval (uvalueMInt (extract v_14988 112 128));
      setRegister (lhs.of_reg v_3443) (mux (ugt (extract v_14988 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 256 0) (concat (lshr (extract v_14991 0 16) v_14994) (concat (lshr (extract v_14991 16 32) v_14994) (concat (lshr (extract v_14991 32 48) v_14994) (concat (lshr (extract v_14991 48 64) v_14994) (concat (lshr (extract v_14991 64 80) v_14994) (concat (lshr (extract v_14991 80 96) v_14994) (concat (lshr (extract v_14991 96 112) v_14994) (concat (lshr (extract v_14991 112 128) v_14994) (concat (lshr (extract v_14991 128 144) v_14994) (concat (lshr (extract v_14991 144 160) v_14994) (concat (lshr (extract v_14991 160 176) v_14994) (concat (lshr (extract v_14991 176 192) v_14994) (concat (lshr (extract v_14991 192 208) v_14994) (concat (lshr (extract v_14991 208 224) v_14994) (concat (lshr (extract v_14991 224 240) v_14994) (lshr (extract v_14991 240 256) v_14994)))))))))))))))));
      pure ()
    pat_end

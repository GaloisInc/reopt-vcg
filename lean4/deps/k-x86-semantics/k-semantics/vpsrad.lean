def vpsrad1 : instruction :=
  definst "vpsrad" $ do
    pattern fun (v_3194 : imm int) (v_3192 : reg (bv 128)) (v_3193 : reg (bv 128)) => do
      v_8603 <- getRegister v_3192;
      v_8604 <- eval (extract v_8603 0 32);
      v_8608 <- eval (handleImmediateWithSignExtend v_3194 8 8);
      v_8613 <- eval (uvalueMInt (mux (ugt (concat (expression.bv_nat 56 0) v_8608) (expression.bv_nat 64 31)) (expression.bv_nat 32 32) (concat (expression.bv_nat 24 0) v_8608)));
      v_8615 <- eval (extract v_8603 32 64);
      v_8620 <- eval (extract v_8603 64 96);
      v_8625 <- eval (extract v_8603 96 128);
      setRegister (lhs.of_reg v_3193) (concat (ashr (mi (bitwidthMInt v_8604) (svalueMInt v_8604)) v_8613) (concat (ashr (mi (bitwidthMInt v_8615) (svalueMInt v_8615)) v_8613) (concat (ashr (mi (bitwidthMInt v_8620) (svalueMInt v_8620)) v_8613) (ashr (mi (bitwidthMInt v_8625) (svalueMInt v_8625)) v_8613))));
      pure ()
    pat_end;
    pattern fun (v_3203 : reg (bv 128)) (v_3204 : reg (bv 128)) (v_3205 : reg (bv 128)) => do
      v_8639 <- getRegister v_3204;
      v_8640 <- eval (extract v_8639 0 32);
      v_8644 <- getRegister v_3203;
      v_8649 <- eval (uvalueMInt (mux (ugt (extract v_8644 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 32 32) (extract v_8644 96 128)));
      v_8651 <- eval (extract v_8639 32 64);
      v_8656 <- eval (extract v_8639 64 96);
      v_8661 <- eval (extract v_8639 96 128);
      setRegister (lhs.of_reg v_3205) (concat (ashr (mi (bitwidthMInt v_8640) (svalueMInt v_8640)) v_8649) (concat (ashr (mi (bitwidthMInt v_8651) (svalueMInt v_8651)) v_8649) (concat (ashr (mi (bitwidthMInt v_8656) (svalueMInt v_8656)) v_8649) (ashr (mi (bitwidthMInt v_8661) (svalueMInt v_8661)) v_8649))));
      pure ()
    pat_end;
    pattern fun (v_3209 : imm int) (v_3210 : reg (bv 256)) (v_3211 : reg (bv 256)) => do
      v_8670 <- getRegister v_3210;
      v_8671 <- eval (extract v_8670 0 32);
      v_8675 <- eval (handleImmediateWithSignExtend v_3209 8 8);
      v_8680 <- eval (uvalueMInt (mux (ugt (concat (expression.bv_nat 56 0) v_8675) (expression.bv_nat 64 31)) (expression.bv_nat 32 32) (concat (expression.bv_nat 24 0) v_8675)));
      v_8682 <- eval (extract v_8670 32 64);
      v_8687 <- eval (extract v_8670 64 96);
      v_8692 <- eval (extract v_8670 96 128);
      v_8697 <- eval (extract v_8670 128 160);
      v_8702 <- eval (extract v_8670 160 192);
      v_8707 <- eval (extract v_8670 192 224);
      v_8712 <- eval (extract v_8670 224 256);
      setRegister (lhs.of_reg v_3211) (concat (ashr (mi (bitwidthMInt v_8671) (svalueMInt v_8671)) v_8680) (concat (ashr (mi (bitwidthMInt v_8682) (svalueMInt v_8682)) v_8680) (concat (ashr (mi (bitwidthMInt v_8687) (svalueMInt v_8687)) v_8680) (concat (ashr (mi (bitwidthMInt v_8692) (svalueMInt v_8692)) v_8680) (concat (ashr (mi (bitwidthMInt v_8697) (svalueMInt v_8697)) v_8680) (concat (ashr (mi (bitwidthMInt v_8702) (svalueMInt v_8702)) v_8680) (concat (ashr (mi (bitwidthMInt v_8707) (svalueMInt v_8707)) v_8680) (ashr (mi (bitwidthMInt v_8712) (svalueMInt v_8712)) v_8680))))))));
      pure ()
    pat_end;
    pattern fun (v_3220 : reg (bv 128)) (v_3221 : reg (bv 256)) (v_3222 : reg (bv 256)) => do
      v_8730 <- getRegister v_3221;
      v_8731 <- eval (extract v_8730 0 32);
      v_8735 <- getRegister v_3220;
      v_8740 <- eval (uvalueMInt (mux (ugt (extract v_8735 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 32 32) (extract v_8735 96 128)));
      v_8742 <- eval (extract v_8730 32 64);
      v_8747 <- eval (extract v_8730 64 96);
      v_8752 <- eval (extract v_8730 96 128);
      v_8757 <- eval (extract v_8730 128 160);
      v_8762 <- eval (extract v_8730 160 192);
      v_8767 <- eval (extract v_8730 192 224);
      v_8772 <- eval (extract v_8730 224 256);
      setRegister (lhs.of_reg v_3222) (concat (ashr (mi (bitwidthMInt v_8731) (svalueMInt v_8731)) v_8740) (concat (ashr (mi (bitwidthMInt v_8742) (svalueMInt v_8742)) v_8740) (concat (ashr (mi (bitwidthMInt v_8747) (svalueMInt v_8747)) v_8740) (concat (ashr (mi (bitwidthMInt v_8752) (svalueMInt v_8752)) v_8740) (concat (ashr (mi (bitwidthMInt v_8757) (svalueMInt v_8757)) v_8740) (concat (ashr (mi (bitwidthMInt v_8762) (svalueMInt v_8762)) v_8740) (concat (ashr (mi (bitwidthMInt v_8767) (svalueMInt v_8767)) v_8740) (ashr (mi (bitwidthMInt v_8772) (svalueMInt v_8772)) v_8740))))))));
      pure ()
    pat_end;
    pattern fun (v_3200 : Mem) (v_3198 : reg (bv 128)) (v_3199 : reg (bv 128)) => do
      v_15307 <- getRegister v_3198;
      v_15308 <- eval (extract v_15307 0 32);
      v_15312 <- evaluateAddress v_3200;
      v_15313 <- load v_15312 16;
      v_15318 <- eval (uvalueMInt (mux (ugt (extract v_15313 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 32 32) (extract v_15313 96 128)));
      v_15320 <- eval (extract v_15307 32 64);
      v_15325 <- eval (extract v_15307 64 96);
      v_15330 <- eval (extract v_15307 96 128);
      setRegister (lhs.of_reg v_3199) (concat (ashr (mi (bitwidthMInt v_15308) (svalueMInt v_15308)) v_15318) (concat (ashr (mi (bitwidthMInt v_15320) (svalueMInt v_15320)) v_15318) (concat (ashr (mi (bitwidthMInt v_15325) (svalueMInt v_15325)) v_15318) (ashr (mi (bitwidthMInt v_15330) (svalueMInt v_15330)) v_15318))));
      pure ()
    pat_end;
    pattern fun (v_3215 : Mem) (v_3216 : reg (bv 256)) (v_3217 : reg (bv 256)) => do
      v_15339 <- getRegister v_3216;
      v_15340 <- eval (extract v_15339 0 32);
      v_15344 <- evaluateAddress v_3215;
      v_15345 <- load v_15344 16;
      v_15350 <- eval (uvalueMInt (mux (ugt (extract v_15345 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 32 32) (extract v_15345 96 128)));
      v_15352 <- eval (extract v_15339 32 64);
      v_15357 <- eval (extract v_15339 64 96);
      v_15362 <- eval (extract v_15339 96 128);
      v_15367 <- eval (extract v_15339 128 160);
      v_15372 <- eval (extract v_15339 160 192);
      v_15377 <- eval (extract v_15339 192 224);
      v_15382 <- eval (extract v_15339 224 256);
      setRegister (lhs.of_reg v_3217) (concat (ashr (mi (bitwidthMInt v_15340) (svalueMInt v_15340)) v_15350) (concat (ashr (mi (bitwidthMInt v_15352) (svalueMInt v_15352)) v_15350) (concat (ashr (mi (bitwidthMInt v_15357) (svalueMInt v_15357)) v_15350) (concat (ashr (mi (bitwidthMInt v_15362) (svalueMInt v_15362)) v_15350) (concat (ashr (mi (bitwidthMInt v_15367) (svalueMInt v_15367)) v_15350) (concat (ashr (mi (bitwidthMInt v_15372) (svalueMInt v_15372)) v_15350) (concat (ashr (mi (bitwidthMInt v_15377) (svalueMInt v_15377)) v_15350) (ashr (mi (bitwidthMInt v_15382) (svalueMInt v_15382)) v_15350))))))));
      pure ()
    pat_end

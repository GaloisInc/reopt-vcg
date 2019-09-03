def pblendw1 : instruction :=
  definst "pblendw" $ do
    pattern fun (v_3239 : imm int) (v_3241 : reg (bv 128)) (v_3242 : reg (bv 128)) => do
      v_6762 <- eval (handleImmediateWithSignExtend v_3239 8 8);
      v_6765 <- getRegister v_3242;
      v_6767 <- getRegister v_3241;
      setRegister (lhs.of_reg v_3242) (concat (mux (eq (extract v_6762 0 1) (expression.bv_nat 1 0)) (extract v_6765 0 16) (extract v_6767 0 16)) (concat (mux (eq (extract v_6762 1 2) (expression.bv_nat 1 0)) (extract v_6765 16 32) (extract v_6767 16 32)) (concat (mux (eq (extract v_6762 2 3) (expression.bv_nat 1 0)) (extract v_6765 32 48) (extract v_6767 32 48)) (concat (mux (eq (extract v_6762 3 4) (expression.bv_nat 1 0)) (extract v_6765 48 64) (extract v_6767 48 64)) (concat (mux (eq (extract v_6762 4 5) (expression.bv_nat 1 0)) (extract v_6765 64 80) (extract v_6767 64 80)) (concat (mux (eq (extract v_6762 5 6) (expression.bv_nat 1 0)) (extract v_6765 80 96) (extract v_6767 80 96)) (concat (mux (eq (extract v_6762 6 7) (expression.bv_nat 1 0)) (extract v_6765 96 112) (extract v_6767 96 112)) (mux (eq (extract v_6762 7 8) (expression.bv_nat 1 0)) (extract v_6765 112 128) (extract v_6767 112 128)))))))));
      pure ()
    pat_end;
    pattern fun (v_3235 : imm int) (v_3234 : Mem) (v_3236 : reg (bv 128)) => do
      v_10814 <- eval (handleImmediateWithSignExtend v_3235 8 8);
      v_10817 <- getRegister v_3236;
      v_10819 <- evaluateAddress v_3234;
      v_10820 <- load v_10819 16;
      setRegister (lhs.of_reg v_3236) (concat (mux (eq (extract v_10814 0 1) (expression.bv_nat 1 0)) (extract v_10817 0 16) (extract v_10820 0 16)) (concat (mux (eq (extract v_10814 1 2) (expression.bv_nat 1 0)) (extract v_10817 16 32) (extract v_10820 16 32)) (concat (mux (eq (extract v_10814 2 3) (expression.bv_nat 1 0)) (extract v_10817 32 48) (extract v_10820 32 48)) (concat (mux (eq (extract v_10814 3 4) (expression.bv_nat 1 0)) (extract v_10817 48 64) (extract v_10820 48 64)) (concat (mux (eq (extract v_10814 4 5) (expression.bv_nat 1 0)) (extract v_10817 64 80) (extract v_10820 64 80)) (concat (mux (eq (extract v_10814 5 6) (expression.bv_nat 1 0)) (extract v_10817 80 96) (extract v_10820 80 96)) (concat (mux (eq (extract v_10814 6 7) (expression.bv_nat 1 0)) (extract v_10817 96 112) (extract v_10820 96 112)) (mux (eq (extract v_10814 7 8) (expression.bv_nat 1 0)) (extract v_10817 112 128) (extract v_10820 112 128)))))))));
      pure ()
    pat_end

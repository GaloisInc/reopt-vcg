def pblendw1 : instruction :=
  definst "pblendw" $ do
    pattern fun (v_3252 : imm int) (v_3253 : reg (bv 128)) (v_3254 : reg (bv 128)) => do
      v_6742 <- eval (handleImmediateWithSignExtend v_3252 8 8);
      v_6745 <- getRegister v_3254;
      v_6747 <- getRegister v_3253;
      setRegister (lhs.of_reg v_3254) (concat (mux (eq (extract v_6742 0 1) (expression.bv_nat 1 0)) (extract v_6745 0 16) (extract v_6747 0 16)) (concat (mux (eq (extract v_6742 1 2) (expression.bv_nat 1 0)) (extract v_6745 16 32) (extract v_6747 16 32)) (concat (mux (eq (extract v_6742 2 3) (expression.bv_nat 1 0)) (extract v_6745 32 48) (extract v_6747 32 48)) (concat (mux (eq (extract v_6742 3 4) (expression.bv_nat 1 0)) (extract v_6745 48 64) (extract v_6747 48 64)) (concat (mux (eq (extract v_6742 4 5) (expression.bv_nat 1 0)) (extract v_6745 64 80) (extract v_6747 64 80)) (concat (mux (eq (extract v_6742 5 6) (expression.bv_nat 1 0)) (extract v_6745 80 96) (extract v_6747 80 96)) (concat (mux (eq (extract v_6742 6 7) (expression.bv_nat 1 0)) (extract v_6745 96 112) (extract v_6747 96 112)) (mux (eq (extract v_6742 7 8) (expression.bv_nat 1 0)) (extract v_6745 112 128) (extract v_6747 112 128)))))))));
      pure ()
    pat_end;
    pattern fun (v_3248 : imm int) (v_3247 : Mem) (v_3249 : reg (bv 128)) => do
      v_10782 <- eval (handleImmediateWithSignExtend v_3248 8 8);
      v_10785 <- getRegister v_3249;
      v_10787 <- evaluateAddress v_3247;
      v_10788 <- load v_10787 16;
      setRegister (lhs.of_reg v_3249) (concat (mux (eq (extract v_10782 0 1) (expression.bv_nat 1 0)) (extract v_10785 0 16) (extract v_10788 0 16)) (concat (mux (eq (extract v_10782 1 2) (expression.bv_nat 1 0)) (extract v_10785 16 32) (extract v_10788 16 32)) (concat (mux (eq (extract v_10782 2 3) (expression.bv_nat 1 0)) (extract v_10785 32 48) (extract v_10788 32 48)) (concat (mux (eq (extract v_10782 3 4) (expression.bv_nat 1 0)) (extract v_10785 48 64) (extract v_10788 48 64)) (concat (mux (eq (extract v_10782 4 5) (expression.bv_nat 1 0)) (extract v_10785 64 80) (extract v_10788 64 80)) (concat (mux (eq (extract v_10782 5 6) (expression.bv_nat 1 0)) (extract v_10785 80 96) (extract v_10788 80 96)) (concat (mux (eq (extract v_10782 6 7) (expression.bv_nat 1 0)) (extract v_10785 96 112) (extract v_10788 96 112)) (mux (eq (extract v_10782 7 8) (expression.bv_nat 1 0)) (extract v_10785 112 128) (extract v_10788 112 128)))))))));
      pure ()
    pat_end

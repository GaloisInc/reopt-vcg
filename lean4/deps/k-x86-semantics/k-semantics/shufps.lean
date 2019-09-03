def shufps1 : instruction :=
  definst "shufps" $ do
    pattern fun (v_3046 : imm int) (v_3048 : reg (bv 128)) (v_3049 : reg (bv 128)) => do
      v_6681 <- eval (handleImmediateWithSignExtend v_3046 8 8);
      v_6685 <- eval (eq (extract v_6681 0 1) (expression.bv_nat 1 1));
      v_6686 <- getRegister v_3048;
      v_6687 <- eval (extract v_6686 0 32);
      v_6688 <- eval (extract v_6686 64 96);
      v_6690 <- eval (extract v_6686 32 64);
      v_6691 <- eval (extract v_6686 96 128);
      v_6697 <- eval (eq (extract v_6681 2 3) (expression.bv_nat 1 1));
      v_6704 <- eval (eq (extract v_6681 4 5) (expression.bv_nat 1 1));
      v_6705 <- getRegister v_3049;
      v_6706 <- eval (extract v_6705 0 32);
      v_6707 <- eval (extract v_6705 64 96);
      v_6709 <- eval (extract v_6705 32 64);
      v_6710 <- eval (extract v_6705 96 128);
      v_6716 <- eval (eq (extract v_6681 6 7) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3049) (concat (mux (eq (extract v_6681 1 2) (expression.bv_nat 1 1)) (mux v_6685 v_6687 v_6688) (mux v_6685 v_6690 v_6691)) (concat (mux (eq (extract v_6681 3 4) (expression.bv_nat 1 1)) (mux v_6697 v_6687 v_6688) (mux v_6697 v_6690 v_6691)) (concat (mux (eq (extract v_6681 5 6) (expression.bv_nat 1 1)) (mux v_6704 v_6706 v_6707) (mux v_6704 v_6709 v_6710)) (mux (eq (extract v_6681 7 8) (expression.bv_nat 1 1)) (mux v_6716 v_6706 v_6707) (mux v_6716 v_6709 v_6710)))));
      pure ()
    pat_end;
    pattern fun (v_3041 : imm int) (v_3042 : Mem) (v_3043 : reg (bv 128)) => do
      v_10205 <- eval (handleImmediateWithSignExtend v_3041 8 8);
      v_10209 <- eval (eq (extract v_10205 0 1) (expression.bv_nat 1 1));
      v_10210 <- evaluateAddress v_3042;
      v_10211 <- load v_10210 16;
      v_10212 <- eval (extract v_10211 0 32);
      v_10213 <- eval (extract v_10211 64 96);
      v_10215 <- eval (extract v_10211 32 64);
      v_10216 <- eval (extract v_10211 96 128);
      v_10222 <- eval (eq (extract v_10205 2 3) (expression.bv_nat 1 1));
      v_10229 <- eval (eq (extract v_10205 4 5) (expression.bv_nat 1 1));
      v_10230 <- getRegister v_3043;
      v_10231 <- eval (extract v_10230 0 32);
      v_10232 <- eval (extract v_10230 64 96);
      v_10234 <- eval (extract v_10230 32 64);
      v_10235 <- eval (extract v_10230 96 128);
      v_10241 <- eval (eq (extract v_10205 6 7) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3043) (concat (mux (eq (extract v_10205 1 2) (expression.bv_nat 1 1)) (mux v_10209 v_10212 v_10213) (mux v_10209 v_10215 v_10216)) (concat (mux (eq (extract v_10205 3 4) (expression.bv_nat 1 1)) (mux v_10222 v_10212 v_10213) (mux v_10222 v_10215 v_10216)) (concat (mux (eq (extract v_10205 5 6) (expression.bv_nat 1 1)) (mux v_10229 v_10231 v_10232) (mux v_10229 v_10234 v_10235)) (mux (eq (extract v_10205 7 8) (expression.bv_nat 1 1)) (mux v_10241 v_10231 v_10232) (mux v_10241 v_10234 v_10235)))));
      pure ()
    pat_end

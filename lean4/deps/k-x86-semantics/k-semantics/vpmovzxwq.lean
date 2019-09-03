def vpmovzxwq1 : instruction :=
  definst "vpmovzxwq" $ do
    pattern fun (v_2789 : reg (bv 128)) (v_2790 : reg (bv 128)) => do
      v_5958 <- getRegister v_2789;
      setRegister (lhs.of_reg v_2790) (concat (expression.bv_nat 48 0) (concat (extract v_5958 96 112) (concat (expression.bv_nat 48 0) (extract v_5958 112 128))));
      pure ()
    pat_end;
    pattern fun (v_2798 : reg (bv 128)) (v_2799 : reg (bv 256)) => do
      v_5969 <- getRegister v_2798;
      setRegister (lhs.of_reg v_2799) (concat (expression.bv_nat 48 0) (concat (extract v_5969 64 80) (concat (expression.bv_nat 48 0) (concat (extract v_5969 80 96) (concat (expression.bv_nat 48 0) (concat (extract v_5969 96 112) (concat (expression.bv_nat 48 0) (extract v_5969 112 128))))))));
      pure ()
    pat_end;
    pattern fun (v_2786 : Mem) (v_2785 : reg (bv 128)) => do
      v_13070 <- evaluateAddress v_2786;
      v_13071 <- load v_13070 4;
      setRegister (lhs.of_reg v_2785) (concat (expression.bv_nat 48 0) (concat (extract v_13071 0 16) (concat (expression.bv_nat 48 0) (extract v_13071 16 32))));
      pure ()
    pat_end;
    pattern fun (v_2794 : Mem) (v_2795 : reg (bv 256)) => do
      v_13078 <- evaluateAddress v_2794;
      v_13079 <- load v_13078 8;
      setRegister (lhs.of_reg v_2795) (concat (expression.bv_nat 48 0) (concat (extract v_13079 0 16) (concat (expression.bv_nat 48 0) (concat (extract v_13079 16 32) (concat (expression.bv_nat 48 0) (concat (extract v_13079 32 48) (concat (expression.bv_nat 48 0) (extract v_13079 48 64))))))));
      pure ()
    pat_end

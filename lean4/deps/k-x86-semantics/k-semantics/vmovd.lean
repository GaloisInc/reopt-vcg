def vmovd1 : instruction :=
  definst "vmovd" $ do
    pattern fun (v_2811 : reg (bv 128)) (v_2810 : reg (bv 32)) => do
      v_4774 <- getRegister v_2811;
      setRegister (lhs.of_reg v_2810) (extract v_4774 96 128);
      pure ()
    pat_end;
    pattern fun (v_2819 : reg (bv 32)) (v_2820 : reg (bv 128)) => do
      v_4781 <- getRegister v_2819;
      setRegister (lhs.of_reg v_2820) (concat (expression.bv_nat 96 0) (concat (extract v_4781 0 8) (extract v_4781 8 32)));
      pure ()
    pat_end;
    pattern fun (v_2807 : reg (bv 128)) (v_2806 : Mem) => do
      v_9321 <- evaluateAddress v_2806;
      v_9322 <- getRegister v_2807;
      store v_9321 (extract v_9322 96 128) 4;
      pure ()
    pat_end;
    pattern fun (v_2815 : Mem) (v_2816 : reg (bv 128)) => do
      v_10167 <- evaluateAddress v_2815;
      v_10168 <- load v_10167 4;
      setRegister (lhs.of_reg v_2816) (concat (expression.bv_nat 96 0) (concat (extract v_10168 0 8) (extract v_10168 8 32)));
      pure ()
    pat_end

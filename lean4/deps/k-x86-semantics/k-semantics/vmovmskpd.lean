def vmovmskpd1 : instruction :=
  definst "vmovmskpd" $ do
    pattern fun (v_2855 : reg (bv 128)) (v_2854 : reg (bv 32)) => do
      v_4809 <- getRegister v_2855;
      setRegister (lhs.of_reg v_2854) (concat (expression.bv_nat 30 0) (concat (extract v_4809 0 1) (extract v_4809 64 65)));
      pure ()
    pat_end;
    pattern fun (v_2860 : reg (bv 256)) (v_2859 : reg (bv 32)) => do
      v_4815 <- getRegister v_2860;
      v_4821 <- eval (extract (add (concat (expression.bv_nat 7 0) (concat (extract v_4815 0 1) (extract v_4815 64 65))) (concat (expression.bv_nat 7 0) (concat (extract v_4815 0 1) (extract v_4815 64 65)))) 1 9);
      setRegister (lhs.of_reg v_2859) (concat (expression.bv_nat 16 0) (extract (add (concat (expression.bv_nat 9 0) (extract (add (concat (expression.bv_nat 1 0) v_4821) (concat (expression.bv_nat 7 0) (concat (extract v_4815 128 129) (extract v_4815 192 193)))) 1 9)) (concat (expression.bv_nat 9 0) v_4821)) 1 17));
      pure ()
    pat_end;
    pattern fun (v_2865 : reg (bv 128)) (v_2863 : reg (bv 64)) => do
      v_4835 <- getRegister v_2865;
      setRegister (lhs.of_reg v_2863) (concat (expression.bv_nat 62 0) (concat (extract v_4835 0 1) (extract v_4835 64 65)));
      pure ()
    pat_end;
    pattern fun (v_2870 : reg (bv 256)) (v_2868 : reg (bv 64)) => do
      v_4841 <- getRegister v_2870;
      v_4847 <- eval (extract (add (concat (expression.bv_nat 7 0) (concat (extract v_4841 0 1) (extract v_4841 64 65))) (concat (expression.bv_nat 7 0) (concat (extract v_4841 0 1) (extract v_4841 64 65)))) 1 9);
      setRegister (lhs.of_reg v_2868) (concat (expression.bv_nat 48 0) (extract (add (concat (expression.bv_nat 9 0) (extract (add (concat (expression.bv_nat 1 0) v_4847) (concat (expression.bv_nat 7 0) (concat (extract v_4841 128 129) (extract v_4841 192 193)))) 1 9)) (concat (expression.bv_nat 9 0) v_4847)) 1 17));
      pure ()
    pat_end

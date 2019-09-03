def vmovmskpd1 : instruction :=
  definst "vmovmskpd" $ do
    pattern fun (v_2866 : reg (bv 128)) (v_2868 : reg (bv 32)) => do
      v_5182 <- getRegister v_2866;
      setRegister (lhs.of_reg v_2868) (concat (expression.bv_nat 30 0) (concat (extract v_5182 0 1) (extract v_5182 64 65)));
      pure ()
    pat_end;
    pattern fun (v_2871 : reg (bv 256)) (v_2873 : reg (bv 32)) => do
      v_5188 <- getRegister v_2871;
      v_5194 <- eval (extract (add (concat (expression.bv_nat 7 0) (concat (extract v_5188 0 1) (extract v_5188 64 65))) (concat (expression.bv_nat 7 0) (concat (extract v_5188 0 1) (extract v_5188 64 65)))) 1 9);
      setRegister (lhs.of_reg v_2873) (concat (expression.bv_nat 16 0) (extract (add (concat (expression.bv_nat 9 0) (extract (add (concat (expression.bv_nat 1 0) v_5194) (concat (expression.bv_nat 7 0) (concat (extract v_5188 128 129) (extract v_5188 192 193)))) 1 9)) (concat (expression.bv_nat 9 0) v_5194)) 1 17));
      pure ()
    pat_end;
    pattern fun (v_2876 : reg (bv 128)) (v_2878 : reg (bv 64)) => do
      v_5208 <- getRegister v_2876;
      setRegister (lhs.of_reg v_2878) (concat (expression.bv_nat 62 0) (concat (extract v_5208 0 1) (extract v_5208 64 65)));
      pure ()
    pat_end;
    pattern fun (v_2881 : reg (bv 256)) (v_2883 : reg (bv 64)) => do
      v_5214 <- getRegister v_2881;
      v_5220 <- eval (extract (add (concat (expression.bv_nat 7 0) (concat (extract v_5214 0 1) (extract v_5214 64 65))) (concat (expression.bv_nat 7 0) (concat (extract v_5214 0 1) (extract v_5214 64 65)))) 1 9);
      setRegister (lhs.of_reg v_2883) (concat (expression.bv_nat 48 0) (extract (add (concat (expression.bv_nat 9 0) (extract (add (concat (expression.bv_nat 1 0) v_5220) (concat (expression.bv_nat 7 0) (concat (extract v_5214 128 129) (extract v_5214 192 193)))) 1 9)) (concat (expression.bv_nat 9 0) v_5220)) 1 17));
      pure ()
    pat_end

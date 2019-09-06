def vmovmskpd1 : instruction :=
  definst "vmovmskpd" $ do
    pattern fun (v_2943 : reg (bv 128)) (v_2942 : reg (bv 32)) => do
      v_4894 <- getRegister v_2943;
      setRegister (lhs.of_reg v_2942) (concat (expression.bv_nat 30 0) (concat (extract v_4894 0 1) (extract v_4894 64 65)));
      pure ()
    pat_end;
    pattern fun (v_2948 : reg (bv 256)) (v_2947 : reg (bv 32)) => do
      v_4900 <- getRegister v_2948;
      v_4906 <- eval (extract (add (concat (expression.bv_nat 7 0) (concat (extract v_4900 0 1) (extract v_4900 64 65))) (concat (expression.bv_nat 7 0) (concat (extract v_4900 0 1) (extract v_4900 64 65)))) 1 9);
      setRegister (lhs.of_reg v_2947) (concat (expression.bv_nat 16 0) (extract (add (concat (expression.bv_nat 9 0) (extract (add (concat (expression.bv_nat 1 0) v_4906) (concat (expression.bv_nat 7 0) (concat (extract v_4900 128 129) (extract v_4900 192 193)))) 1 9)) (concat (expression.bv_nat 9 0) v_4906)) 1 17));
      pure ()
    pat_end;
    pattern fun (v_2953 : reg (bv 128)) (v_2952 : reg (bv 64)) => do
      v_4920 <- getRegister v_2953;
      setRegister (lhs.of_reg v_2952) (concat (expression.bv_nat 62 0) (concat (extract v_4920 0 1) (extract v_4920 64 65)));
      pure ()
    pat_end;
    pattern fun (v_2958 : reg (bv 256)) (v_2957 : reg (bv 64)) => do
      v_4926 <- getRegister v_2958;
      v_4932 <- eval (extract (add (concat (expression.bv_nat 7 0) (concat (extract v_4926 0 1) (extract v_4926 64 65))) (concat (expression.bv_nat 7 0) (concat (extract v_4926 0 1) (extract v_4926 64 65)))) 1 9);
      setRegister (lhs.of_reg v_2957) (concat (expression.bv_nat 48 0) (extract (add (concat (expression.bv_nat 9 0) (extract (add (concat (expression.bv_nat 1 0) v_4932) (concat (expression.bv_nat 7 0) (concat (extract v_4926 128 129) (extract v_4926 192 193)))) 1 9)) (concat (expression.bv_nat 9 0) v_4932)) 1 17));
      pure ()
    pat_end

def vmovmskpd1 : instruction :=
  definst "vmovmskpd" $ do
    pattern fun (v_2918 : reg (bv 128)) (v_2917 : reg (bv 32)) => do
      v_4867 <- getRegister v_2918;
      setRegister (lhs.of_reg v_2917) (concat (expression.bv_nat 30 0) (concat (extract v_4867 0 1) (extract v_4867 64 65)));
      pure ()
    pat_end;
    pattern fun (v_2924 : reg (bv 256)) (v_2922 : reg (bv 32)) => do
      v_4873 <- getRegister v_2924;
      v_4879 <- eval (extract (add (concat (expression.bv_nat 7 0) (concat (extract v_4873 0 1) (extract v_4873 64 65))) (concat (expression.bv_nat 7 0) (concat (extract v_4873 0 1) (extract v_4873 64 65)))) 1 9);
      setRegister (lhs.of_reg v_2922) (concat (expression.bv_nat 16 0) (extract (add (concat (expression.bv_nat 9 0) (extract (add (concat (expression.bv_nat 1 0) v_4879) (concat (expression.bv_nat 7 0) (concat (extract v_4873 128 129) (extract v_4873 192 193)))) 1 9)) (concat (expression.bv_nat 9 0) v_4879)) 1 17));
      pure ()
    pat_end;
    pattern fun (v_2927 : reg (bv 128)) (v_2928 : reg (bv 64)) => do
      v_4893 <- getRegister v_2927;
      setRegister (lhs.of_reg v_2928) (concat (expression.bv_nat 62 0) (concat (extract v_4893 0 1) (extract v_4893 64 65)));
      pure ()
    pat_end;
    pattern fun (v_2934 : reg (bv 256)) (v_2932 : reg (bv 64)) => do
      v_4899 <- getRegister v_2934;
      v_4905 <- eval (extract (add (concat (expression.bv_nat 7 0) (concat (extract v_4899 0 1) (extract v_4899 64 65))) (concat (expression.bv_nat 7 0) (concat (extract v_4899 0 1) (extract v_4899 64 65)))) 1 9);
      setRegister (lhs.of_reg v_2932) (concat (expression.bv_nat 48 0) (extract (add (concat (expression.bv_nat 9 0) (extract (add (concat (expression.bv_nat 1 0) v_4905) (concat (expression.bv_nat 7 0) (concat (extract v_4899 128 129) (extract v_4899 192 193)))) 1 9)) (concat (expression.bv_nat 9 0) v_4905)) 1 17));
      pure ()
    pat_end

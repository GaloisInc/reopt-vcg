def vmovmskpd : instruction :=
  definst "vmovmskpd" $ do
    pattern fun (xmm_0 : reg (bv 128)) (r32_1 : reg (bv 32)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      setRegister (lhs.of_reg r32_1) (concat (expression.bv_nat 30 0) (concat (extract v_2 0 1) (extract v_2 64 65)));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (r64_1 : reg (bv 64)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      setRegister (lhs.of_reg r64_1) (concat (expression.bv_nat 62 0) (concat (extract v_2 0 1) (extract v_2 64 65)));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (r32_1 : reg (bv 32)) => do
      v_2 <- getRegister (lhs.of_reg ymm_0);
      v_3 <- eval (extract (add (concat (expression.bv_nat 7 0) (concat (extract v_2 0 1) (extract v_2 64 65))) (concat (expression.bv_nat 7 0) (concat (extract v_2 0 1) (extract v_2 64 65)))) 1 9);
      setRegister (lhs.of_reg r32_1) (concat (expression.bv_nat 16 0) (extract (add (concat (expression.bv_nat 9 0) (extract (add (concat (expression.bv_nat 1 0) v_3) (concat (expression.bv_nat 7 0) (concat (extract v_2 128 129) (extract v_2 192 193)))) 1 9)) (concat (expression.bv_nat 9 0) v_3)) 1 17));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (r64_1 : reg (bv 64)) => do
      v_2 <- getRegister (lhs.of_reg ymm_0);
      v_3 <- eval (extract (add (concat (expression.bv_nat 7 0) (concat (extract v_2 0 1) (extract v_2 64 65))) (concat (expression.bv_nat 7 0) (concat (extract v_2 0 1) (extract v_2 64 65)))) 1 9);
      setRegister (lhs.of_reg r64_1) (concat (expression.bv_nat 48 0) (extract (add (concat (expression.bv_nat 9 0) (extract (add (concat (expression.bv_nat 1 0) v_3) (concat (expression.bv_nat 7 0) (concat (extract v_2 128 129) (extract v_2 192 193)))) 1 9)) (concat (expression.bv_nat 9 0) v_3)) 1 17));
      pure ()
    pat_end

def vmovmskps : instruction :=
  definst "vmovmskps" $ do
    pattern fun (xmm_0 : reg (bv 128)) (r32_1 : reg (bv 32)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      setRegister (lhs.of_reg r32_1) (concat (expression.bv_nat 28 0) (concat (extract v_2 0 1) (concat (extract v_2 32 33) (concat (extract v_2 64 65) (extract v_2 96 97)))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (r64_1 : reg (bv 64)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      setRegister (lhs.of_reg r64_1) (concat (expression.bv_nat 60 0) (concat (extract v_2 0 1) (concat (extract v_2 32 33) (concat (extract v_2 64 65) (extract v_2 96 97)))));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (r32_1 : reg (bv 32)) => do
      v_2 <- getRegister (lhs.of_reg ymm_0);
      setRegister (lhs.of_reg r32_1) (concat (expression.bv_nat 24 0) (concat (extract v_2 0 1) (concat (extract v_2 32 33) (concat (extract v_2 64 65) (concat (extract v_2 96 97) (concat (extract v_2 128 129) (concat (extract v_2 160 161) (concat (extract v_2 192 193) (extract v_2 224 225)))))))));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (r64_1 : reg (bv 64)) => do
      v_2 <- getRegister (lhs.of_reg ymm_0);
      setRegister (lhs.of_reg r64_1) (concat (expression.bv_nat 56 0) (concat (extract v_2 0 1) (concat (extract v_2 32 33) (concat (extract v_2 64 65) (concat (extract v_2 96 97) (concat (extract v_2 128 129) (concat (extract v_2 160 161) (concat (extract v_2 192 193) (extract v_2 224 225)))))))));
      pure ()
    pat_end

def pmovmskb1 : instruction :=
  definst "pmovmskb" $ do
    pattern fun (xmm_0 : reg (bv 128)) (r32_1 : reg (bv 32)) => do
      v_2 <- getRegister xmm_0;
      setRegister (lhs.of_reg r32_1) (concat (expression.bv_nat 16 0) (concat (extract v_2 0 1) (concat (extract v_2 8 9) (concat (extract v_2 16 17) (concat (extract v_2 24 25) (concat (extract v_2 32 33) (concat (extract v_2 40 41) (concat (extract v_2 48 49) (concat (extract v_2 56 57) (concat (extract v_2 64 65) (concat (extract v_2 72 73) (concat (extract v_2 80 81) (concat (extract v_2 88 89) (concat (extract v_2 96 97) (concat (extract v_2 104 105) (concat (extract v_2 112 113) (extract v_2 120 121)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (r64_1 : reg (bv 64)) => do
      v_2 <- getRegister xmm_0;
      setRegister (lhs.of_reg r64_1) (concat (expression.bv_nat 48 0) (concat (extract v_2 0 1) (concat (extract v_2 8 9) (concat (extract v_2 16 17) (concat (extract v_2 24 25) (concat (extract v_2 32 33) (concat (extract v_2 40 41) (concat (extract v_2 48 49) (concat (extract v_2 56 57) (concat (extract v_2 64 65) (concat (extract v_2 72 73) (concat (extract v_2 80 81) (concat (extract v_2 88 89) (concat (extract v_2 96 97) (concat (extract v_2 104 105) (concat (extract v_2 112 113) (extract v_2 120 121)))))))))))))))));
      pure ()
    pat_end

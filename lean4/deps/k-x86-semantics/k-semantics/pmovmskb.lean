def pmovmskb1 : instruction :=
  definst "pmovmskb" $ do
    pattern fun (v_2652 : reg (bv 128)) (v_2653 : reg (bv 32)) => do
      v_5396 <- getRegister v_2652;
      setRegister (lhs.of_reg v_2653) (concat (expression.bv_nat 16 0) (concat (extract v_5396 0 1) (concat (extract v_5396 8 9) (concat (extract v_5396 16 17) (concat (extract v_5396 24 25) (concat (extract v_5396 32 33) (concat (extract v_5396 40 41) (concat (extract v_5396 48 49) (concat (extract v_5396 56 57) (concat (extract v_5396 64 65) (concat (extract v_5396 72 73) (concat (extract v_5396 80 81) (concat (extract v_5396 88 89) (concat (extract v_5396 96 97) (concat (extract v_5396 104 105) (concat (extract v_5396 112 113) (extract v_5396 120 121)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2657 : reg (bv 128)) (v_2659 : reg (bv 64)) => do
      v_5430 <- getRegister v_2657;
      setRegister (lhs.of_reg v_2659) (concat (expression.bv_nat 48 0) (concat (extract v_5430 0 1) (concat (extract v_5430 8 9) (concat (extract v_5430 16 17) (concat (extract v_5430 24 25) (concat (extract v_5430 32 33) (concat (extract v_5430 40 41) (concat (extract v_5430 48 49) (concat (extract v_5430 56 57) (concat (extract v_5430 64 65) (concat (extract v_5430 72 73) (concat (extract v_5430 80 81) (concat (extract v_5430 88 89) (concat (extract v_5430 96 97) (concat (extract v_5430 104 105) (concat (extract v_5430 112 113) (extract v_5430 120 121)))))))))))))))));
      pure ()
    pat_end

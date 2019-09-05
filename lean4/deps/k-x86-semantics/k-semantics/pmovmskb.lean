def pmovmskb1 : instruction :=
  definst "pmovmskb" $ do
    pattern fun (v_2715 : reg (bv 128)) (v_2716 : reg (bv 32)) => do
      v_5360 <- getRegister v_2715;
      setRegister (lhs.of_reg v_2716) (concat (expression.bv_nat 16 0) (concat (extract v_5360 0 1) (concat (extract v_5360 8 9) (concat (extract v_5360 16 17) (concat (extract v_5360 24 25) (concat (extract v_5360 32 33) (concat (extract v_5360 40 41) (concat (extract v_5360 48 49) (concat (extract v_5360 56 57) (concat (extract v_5360 64 65) (concat (extract v_5360 72 73) (concat (extract v_5360 80 81) (concat (extract v_5360 88 89) (concat (extract v_5360 96 97) (concat (extract v_5360 104 105) (concat (extract v_5360 112 113) (extract v_5360 120 121)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2721 : reg (bv 128)) (v_2720 : reg (bv 64)) => do
      v_5394 <- getRegister v_2721;
      setRegister (lhs.of_reg v_2720) (concat (expression.bv_nat 48 0) (concat (extract v_5394 0 1) (concat (extract v_5394 8 9) (concat (extract v_5394 16 17) (concat (extract v_5394 24 25) (concat (extract v_5394 32 33) (concat (extract v_5394 40 41) (concat (extract v_5394 48 49) (concat (extract v_5394 56 57) (concat (extract v_5394 64 65) (concat (extract v_5394 72 73) (concat (extract v_5394 80 81) (concat (extract v_5394 88 89) (concat (extract v_5394 96 97) (concat (extract v_5394 104 105) (concat (extract v_5394 112 113) (extract v_5394 120 121)))))))))))))))));
      pure ()
    pat_end

def pmovmskb1 : instruction :=
  definst "pmovmskb" $ do
    pattern fun (v_2743 : reg (bv 128)) (v_2744 : reg (bv 32)) => do
      v_5387 <- getRegister v_2743;
      setRegister (lhs.of_reg v_2744) (concat (expression.bv_nat 16 0) (concat (extract v_5387 0 1) (concat (extract v_5387 8 9) (concat (extract v_5387 16 17) (concat (extract v_5387 24 25) (concat (extract v_5387 32 33) (concat (extract v_5387 40 41) (concat (extract v_5387 48 49) (concat (extract v_5387 56 57) (concat (extract v_5387 64 65) (concat (extract v_5387 72 73) (concat (extract v_5387 80 81) (concat (extract v_5387 88 89) (concat (extract v_5387 96 97) (concat (extract v_5387 104 105) (concat (extract v_5387 112 113) (extract v_5387 120 121)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2749 : reg (bv 128)) (v_2748 : reg (bv 64)) => do
      v_5421 <- getRegister v_2749;
      setRegister (lhs.of_reg v_2748) (concat (expression.bv_nat 48 0) (concat (extract v_5421 0 1) (concat (extract v_5421 8 9) (concat (extract v_5421 16 17) (concat (extract v_5421 24 25) (concat (extract v_5421 32 33) (concat (extract v_5421 40 41) (concat (extract v_5421 48 49) (concat (extract v_5421 56 57) (concat (extract v_5421 64 65) (concat (extract v_5421 72 73) (concat (extract v_5421 80 81) (concat (extract v_5421 88 89) (concat (extract v_5421 96 97) (concat (extract v_5421 104 105) (concat (extract v_5421 112 113) (extract v_5421 120 121)))))))))))))))));
      pure ()
    pat_end

def pmovmskb1 : instruction :=
  definst "pmovmskb" $ do
    pattern fun (v_2666 : reg (bv 128)) (v_2668 : reg (bv 32)) => do
      v_5329 <- getRegister v_2666;
      setRegister (lhs.of_reg v_2668) (concat (expression.bv_nat 16 0) (concat (extract v_5329 0 1) (concat (extract v_5329 8 9) (concat (extract v_5329 16 17) (concat (extract v_5329 24 25) (concat (extract v_5329 32 33) (concat (extract v_5329 40 41) (concat (extract v_5329 48 49) (concat (extract v_5329 56 57) (concat (extract v_5329 64 65) (concat (extract v_5329 72 73) (concat (extract v_5329 80 81) (concat (extract v_5329 88 89) (concat (extract v_5329 96 97) (concat (extract v_5329 104 105) (concat (extract v_5329 112 113) (extract v_5329 120 121)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2671 : reg (bv 128)) (v_2672 : reg (bv 64)) => do
      v_5363 <- getRegister v_2671;
      setRegister (lhs.of_reg v_2672) (concat (expression.bv_nat 48 0) (concat (extract v_5363 0 1) (concat (extract v_5363 8 9) (concat (extract v_5363 16 17) (concat (extract v_5363 24 25) (concat (extract v_5363 32 33) (concat (extract v_5363 40 41) (concat (extract v_5363 48 49) (concat (extract v_5363 56 57) (concat (extract v_5363 64 65) (concat (extract v_5363 72 73) (concat (extract v_5363 80 81) (concat (extract v_5363 88 89) (concat (extract v_5363 96 97) (concat (extract v_5363 104 105) (concat (extract v_5363 112 113) (extract v_5363 120 121)))))))))))))))));
      pure ()
    pat_end

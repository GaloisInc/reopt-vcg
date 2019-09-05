def vpmovmskb1 : instruction :=
  definst "vpmovmskb" $ do
    pattern fun (v_2633 : reg (bv 128)) (v_2632 : reg (bv 32)) => do
      v_5265 <- getRegister v_2633;
      setRegister (lhs.of_reg v_2632) (concat (expression.bv_nat 16 0) (concat (extract v_5265 0 1) (concat (extract v_5265 8 9) (concat (extract v_5265 16 17) (concat (extract v_5265 24 25) (concat (extract v_5265 32 33) (concat (extract v_5265 40 41) (concat (extract v_5265 48 49) (concat (extract v_5265 56 57) (concat (extract v_5265 64 65) (concat (extract v_5265 72 73) (concat (extract v_5265 80 81) (concat (extract v_5265 88 89) (concat (extract v_5265 96 97) (concat (extract v_5265 104 105) (concat (extract v_5265 112 113) (extract v_5265 120 121)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2637 : reg (bv 256)) (v_2638 : reg (bv 32)) => do
      v_5299 <- getRegister v_2637;
      setRegister (lhs.of_reg v_2638) (concat (extract v_5299 0 1) (concat (extract v_5299 8 9) (concat (extract v_5299 16 17) (concat (extract v_5299 24 25) (concat (extract v_5299 32 33) (concat (extract v_5299 40 41) (concat (extract v_5299 48 49) (concat (extract v_5299 56 57) (concat (extract v_5299 64 65) (concat (extract v_5299 72 73) (concat (extract v_5299 80 81) (concat (extract v_5299 88 89) (concat (extract v_5299 96 97) (concat (extract v_5299 104 105) (concat (extract v_5299 112 113) (concat (extract v_5299 120 121) (concat (extract v_5299 128 129) (concat (extract v_5299 136 137) (concat (extract v_5299 144 145) (concat (extract v_5299 152 153) (concat (extract v_5299 160 161) (concat (extract v_5299 168 169) (concat (extract v_5299 176 177) (concat (extract v_5299 184 185) (concat (extract v_5299 192 193) (concat (extract v_5299 200 201) (concat (extract v_5299 208 209) (concat (extract v_5299 216 217) (concat (extract v_5299 224 225) (concat (extract v_5299 232 233) (concat (extract v_5299 240 241) (extract v_5299 248 249))))))))))))))))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2643 : reg (bv 128)) (v_2641 : reg (bv 64)) => do
      v_5364 <- getRegister v_2643;
      setRegister (lhs.of_reg v_2641) (concat (expression.bv_nat 48 0) (concat (extract v_5364 0 1) (concat (extract v_5364 8 9) (concat (extract v_5364 16 17) (concat (extract v_5364 24 25) (concat (extract v_5364 32 33) (concat (extract v_5364 40 41) (concat (extract v_5364 48 49) (concat (extract v_5364 56 57) (concat (extract v_5364 64 65) (concat (extract v_5364 72 73) (concat (extract v_5364 80 81) (concat (extract v_5364 88 89) (concat (extract v_5364 96 97) (concat (extract v_5364 104 105) (concat (extract v_5364 112 113) (extract v_5364 120 121)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2648 : reg (bv 256)) (v_2646 : reg (bv 64)) => do
      v_5398 <- getRegister v_2648;
      setRegister (lhs.of_reg v_2646) (concat (expression.bv_nat 32 0) (concat (extract v_5398 0 1) (concat (extract v_5398 8 9) (concat (extract v_5398 16 17) (concat (extract v_5398 24 25) (concat (extract v_5398 32 33) (concat (extract v_5398 40 41) (concat (extract v_5398 48 49) (concat (extract v_5398 56 57) (concat (extract v_5398 64 65) (concat (extract v_5398 72 73) (concat (extract v_5398 80 81) (concat (extract v_5398 88 89) (concat (extract v_5398 96 97) (concat (extract v_5398 104 105) (concat (extract v_5398 112 113) (concat (extract v_5398 120 121) (concat (extract v_5398 128 129) (concat (extract v_5398 136 137) (concat (extract v_5398 144 145) (concat (extract v_5398 152 153) (concat (extract v_5398 160 161) (concat (extract v_5398 168 169) (concat (extract v_5398 176 177) (concat (extract v_5398 184 185) (concat (extract v_5398 192 193) (concat (extract v_5398 200 201) (concat (extract v_5398 208 209) (concat (extract v_5398 216 217) (concat (extract v_5398 224 225) (concat (extract v_5398 232 233) (concat (extract v_5398 240 241) (extract v_5398 248 249)))))))))))))))))))))))))))))))));
      pure ()
    pat_end

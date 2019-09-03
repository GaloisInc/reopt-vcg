def vpmovmskb1 : instruction :=
  definst "vpmovmskb" $ do
    pattern fun (v_2580 : reg (bv 128)) (v_2578 : reg (bv 32)) => do
      v_5214 <- getRegister v_2580;
      setRegister (lhs.of_reg v_2578) (concat (expression.bv_nat 16 0) (concat (extract v_5214 0 1) (concat (extract v_5214 8 9) (concat (extract v_5214 16 17) (concat (extract v_5214 24 25) (concat (extract v_5214 32 33) (concat (extract v_5214 40 41) (concat (extract v_5214 48 49) (concat (extract v_5214 56 57) (concat (extract v_5214 64 65) (concat (extract v_5214 72 73) (concat (extract v_5214 80 81) (concat (extract v_5214 88 89) (concat (extract v_5214 96 97) (concat (extract v_5214 104 105) (concat (extract v_5214 112 113) (extract v_5214 120 121)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2586 : reg (bv 256)) (v_2583 : reg (bv 32)) => do
      v_5248 <- getRegister v_2586;
      setRegister (lhs.of_reg v_2583) (concat (extract v_5248 0 1) (concat (extract v_5248 8 9) (concat (extract v_5248 16 17) (concat (extract v_5248 24 25) (concat (extract v_5248 32 33) (concat (extract v_5248 40 41) (concat (extract v_5248 48 49) (concat (extract v_5248 56 57) (concat (extract v_5248 64 65) (concat (extract v_5248 72 73) (concat (extract v_5248 80 81) (concat (extract v_5248 88 89) (concat (extract v_5248 96 97) (concat (extract v_5248 104 105) (concat (extract v_5248 112 113) (concat (extract v_5248 120 121) (concat (extract v_5248 128 129) (concat (extract v_5248 136 137) (concat (extract v_5248 144 145) (concat (extract v_5248 152 153) (concat (extract v_5248 160 161) (concat (extract v_5248 168 169) (concat (extract v_5248 176 177) (concat (extract v_5248 184 185) (concat (extract v_5248 192 193) (concat (extract v_5248 200 201) (concat (extract v_5248 208 209) (concat (extract v_5248 216 217) (concat (extract v_5248 224 225) (concat (extract v_5248 232 233) (concat (extract v_5248 240 241) (extract v_5248 248 249))))))))))))))))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2590 : reg (bv 128)) (v_2589 : reg (bv 64)) => do
      v_5313 <- getRegister v_2590;
      setRegister (lhs.of_reg v_2589) (concat (expression.bv_nat 48 0) (concat (extract v_5313 0 1) (concat (extract v_5313 8 9) (concat (extract v_5313 16 17) (concat (extract v_5313 24 25) (concat (extract v_5313 32 33) (concat (extract v_5313 40 41) (concat (extract v_5313 48 49) (concat (extract v_5313 56 57) (concat (extract v_5313 64 65) (concat (extract v_5313 72 73) (concat (extract v_5313 80 81) (concat (extract v_5313 88 89) (concat (extract v_5313 96 97) (concat (extract v_5313 104 105) (concat (extract v_5313 112 113) (extract v_5313 120 121)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2596 : reg (bv 256)) (v_2594 : reg (bv 64)) => do
      v_5347 <- getRegister v_2596;
      setRegister (lhs.of_reg v_2594) (concat (expression.bv_nat 32 0) (concat (extract v_5347 0 1) (concat (extract v_5347 8 9) (concat (extract v_5347 16 17) (concat (extract v_5347 24 25) (concat (extract v_5347 32 33) (concat (extract v_5347 40 41) (concat (extract v_5347 48 49) (concat (extract v_5347 56 57) (concat (extract v_5347 64 65) (concat (extract v_5347 72 73) (concat (extract v_5347 80 81) (concat (extract v_5347 88 89) (concat (extract v_5347 96 97) (concat (extract v_5347 104 105) (concat (extract v_5347 112 113) (concat (extract v_5347 120 121) (concat (extract v_5347 128 129) (concat (extract v_5347 136 137) (concat (extract v_5347 144 145) (concat (extract v_5347 152 153) (concat (extract v_5347 160 161) (concat (extract v_5347 168 169) (concat (extract v_5347 176 177) (concat (extract v_5347 184 185) (concat (extract v_5347 192 193) (concat (extract v_5347 200 201) (concat (extract v_5347 208 209) (concat (extract v_5347 216 217) (concat (extract v_5347 224 225) (concat (extract v_5347 232 233) (concat (extract v_5347 240 241) (extract v_5347 248 249)))))))))))))))))))))))))))))))));
      pure ()
    pat_end

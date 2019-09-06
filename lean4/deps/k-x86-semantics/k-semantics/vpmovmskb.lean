def vpmovmskb1 : instruction :=
  definst "vpmovmskb" $ do
    pattern fun (v_2660 : reg (bv 128)) (v_2659 : reg (bv 32)) => do
      v_5292 <- getRegister v_2660;
      setRegister (lhs.of_reg v_2659) (concat (expression.bv_nat 16 0) (concat (extract v_5292 0 1) (concat (extract v_5292 8 9) (concat (extract v_5292 16 17) (concat (extract v_5292 24 25) (concat (extract v_5292 32 33) (concat (extract v_5292 40 41) (concat (extract v_5292 48 49) (concat (extract v_5292 56 57) (concat (extract v_5292 64 65) (concat (extract v_5292 72 73) (concat (extract v_5292 80 81) (concat (extract v_5292 88 89) (concat (extract v_5292 96 97) (concat (extract v_5292 104 105) (concat (extract v_5292 112 113) (extract v_5292 120 121)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2665 : reg (bv 256)) (v_2664 : reg (bv 32)) => do
      v_5326 <- getRegister v_2665;
      setRegister (lhs.of_reg v_2664) (concat (extract v_5326 0 1) (concat (extract v_5326 8 9) (concat (extract v_5326 16 17) (concat (extract v_5326 24 25) (concat (extract v_5326 32 33) (concat (extract v_5326 40 41) (concat (extract v_5326 48 49) (concat (extract v_5326 56 57) (concat (extract v_5326 64 65) (concat (extract v_5326 72 73) (concat (extract v_5326 80 81) (concat (extract v_5326 88 89) (concat (extract v_5326 96 97) (concat (extract v_5326 104 105) (concat (extract v_5326 112 113) (concat (extract v_5326 120 121) (concat (extract v_5326 128 129) (concat (extract v_5326 136 137) (concat (extract v_5326 144 145) (concat (extract v_5326 152 153) (concat (extract v_5326 160 161) (concat (extract v_5326 168 169) (concat (extract v_5326 176 177) (concat (extract v_5326 184 185) (concat (extract v_5326 192 193) (concat (extract v_5326 200 201) (concat (extract v_5326 208 209) (concat (extract v_5326 216 217) (concat (extract v_5326 224 225) (concat (extract v_5326 232 233) (concat (extract v_5326 240 241) (extract v_5326 248 249))))))))))))))))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2669 : reg (bv 128)) (v_2670 : reg (bv 64)) => do
      v_5391 <- getRegister v_2669;
      setRegister (lhs.of_reg v_2670) (concat (expression.bv_nat 48 0) (concat (extract v_5391 0 1) (concat (extract v_5391 8 9) (concat (extract v_5391 16 17) (concat (extract v_5391 24 25) (concat (extract v_5391 32 33) (concat (extract v_5391 40 41) (concat (extract v_5391 48 49) (concat (extract v_5391 56 57) (concat (extract v_5391 64 65) (concat (extract v_5391 72 73) (concat (extract v_5391 80 81) (concat (extract v_5391 88 89) (concat (extract v_5391 96 97) (concat (extract v_5391 104 105) (concat (extract v_5391 112 113) (extract v_5391 120 121)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2674 : reg (bv 256)) (v_2675 : reg (bv 64)) => do
      v_5425 <- getRegister v_2674;
      setRegister (lhs.of_reg v_2675) (concat (expression.bv_nat 32 0) (concat (extract v_5425 0 1) (concat (extract v_5425 8 9) (concat (extract v_5425 16 17) (concat (extract v_5425 24 25) (concat (extract v_5425 32 33) (concat (extract v_5425 40 41) (concat (extract v_5425 48 49) (concat (extract v_5425 56 57) (concat (extract v_5425 64 65) (concat (extract v_5425 72 73) (concat (extract v_5425 80 81) (concat (extract v_5425 88 89) (concat (extract v_5425 96 97) (concat (extract v_5425 104 105) (concat (extract v_5425 112 113) (concat (extract v_5425 120 121) (concat (extract v_5425 128 129) (concat (extract v_5425 136 137) (concat (extract v_5425 144 145) (concat (extract v_5425 152 153) (concat (extract v_5425 160 161) (concat (extract v_5425 168 169) (concat (extract v_5425 176 177) (concat (extract v_5425 184 185) (concat (extract v_5425 192 193) (concat (extract v_5425 200 201) (concat (extract v_5425 208 209) (concat (extract v_5425 216 217) (concat (extract v_5425 224 225) (concat (extract v_5425 232 233) (concat (extract v_5425 240 241) (extract v_5425 248 249)))))))))))))))))))))))))))))))));
      pure ()
    pat_end

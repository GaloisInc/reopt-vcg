def vpmovmskb1 : instruction :=
  definst "vpmovmskb" $ do
    pattern fun (v_2567 : reg (bv 128)) (v_2568 : reg (bv 32)) => do
      v_5201 <- getRegister v_2567;
      setRegister (lhs.of_reg v_2568) (concat (expression.bv_nat 16 0) (concat (extract v_5201 0 1) (concat (extract v_5201 8 9) (concat (extract v_5201 16 17) (concat (extract v_5201 24 25) (concat (extract v_5201 32 33) (concat (extract v_5201 40 41) (concat (extract v_5201 48 49) (concat (extract v_5201 56 57) (concat (extract v_5201 64 65) (concat (extract v_5201 72 73) (concat (extract v_5201 80 81) (concat (extract v_5201 88 89) (concat (extract v_5201 96 97) (concat (extract v_5201 104 105) (concat (extract v_5201 112 113) (extract v_5201 120 121)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2573 : reg (bv 256)) (v_2572 : reg (bv 32)) => do
      v_5235 <- getRegister v_2573;
      setRegister (lhs.of_reg v_2572) (concat (extract v_5235 0 1) (concat (extract v_5235 8 9) (concat (extract v_5235 16 17) (concat (extract v_5235 24 25) (concat (extract v_5235 32 33) (concat (extract v_5235 40 41) (concat (extract v_5235 48 49) (concat (extract v_5235 56 57) (concat (extract v_5235 64 65) (concat (extract v_5235 72 73) (concat (extract v_5235 80 81) (concat (extract v_5235 88 89) (concat (extract v_5235 96 97) (concat (extract v_5235 104 105) (concat (extract v_5235 112 113) (concat (extract v_5235 120 121) (concat (extract v_5235 128 129) (concat (extract v_5235 136 137) (concat (extract v_5235 144 145) (concat (extract v_5235 152 153) (concat (extract v_5235 160 161) (concat (extract v_5235 168 169) (concat (extract v_5235 176 177) (concat (extract v_5235 184 185) (concat (extract v_5235 192 193) (concat (extract v_5235 200 201) (concat (extract v_5235 208 209) (concat (extract v_5235 216 217) (concat (extract v_5235 224 225) (concat (extract v_5235 232 233) (concat (extract v_5235 240 241) (extract v_5235 248 249))))))))))))))))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2577 : reg (bv 128)) (v_2578 : reg (bv 64)) => do
      v_5300 <- getRegister v_2577;
      setRegister (lhs.of_reg v_2578) (concat (expression.bv_nat 48 0) (concat (extract v_5300 0 1) (concat (extract v_5300 8 9) (concat (extract v_5300 16 17) (concat (extract v_5300 24 25) (concat (extract v_5300 32 33) (concat (extract v_5300 40 41) (concat (extract v_5300 48 49) (concat (extract v_5300 56 57) (concat (extract v_5300 64 65) (concat (extract v_5300 72 73) (concat (extract v_5300 80 81) (concat (extract v_5300 88 89) (concat (extract v_5300 96 97) (concat (extract v_5300 104 105) (concat (extract v_5300 112 113) (extract v_5300 120 121)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2582 : reg (bv 256)) (v_2583 : reg (bv 64)) => do
      v_5334 <- getRegister v_2582;
      setRegister (lhs.of_reg v_2583) (concat (expression.bv_nat 32 0) (concat (extract v_5334 0 1) (concat (extract v_5334 8 9) (concat (extract v_5334 16 17) (concat (extract v_5334 24 25) (concat (extract v_5334 32 33) (concat (extract v_5334 40 41) (concat (extract v_5334 48 49) (concat (extract v_5334 56 57) (concat (extract v_5334 64 65) (concat (extract v_5334 72 73) (concat (extract v_5334 80 81) (concat (extract v_5334 88 89) (concat (extract v_5334 96 97) (concat (extract v_5334 104 105) (concat (extract v_5334 112 113) (concat (extract v_5334 120 121) (concat (extract v_5334 128 129) (concat (extract v_5334 136 137) (concat (extract v_5334 144 145) (concat (extract v_5334 152 153) (concat (extract v_5334 160 161) (concat (extract v_5334 168 169) (concat (extract v_5334 176 177) (concat (extract v_5334 184 185) (concat (extract v_5334 192 193) (concat (extract v_5334 200 201) (concat (extract v_5334 208 209) (concat (extract v_5334 216 217) (concat (extract v_5334 224 225) (concat (extract v_5334 232 233) (concat (extract v_5334 240 241) (extract v_5334 248 249)))))))))))))))))))))))))))))))));
      pure ()
    pat_end

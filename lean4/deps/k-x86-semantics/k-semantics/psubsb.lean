def psubsb1 : instruction :=
  definst "psubsb" $ do
    pattern fun (v_3199 : reg (bv 128)) (v_3200 : reg (bv 128)) => do
      v_8079 <- getRegister v_3200;
      v_8082 <- getRegister v_3199;
      v_8085 <- eval (sub (sext (extract v_8079 0 8) 10) (sext (extract v_8082 0 8) 10));
      v_8095 <- eval (sub (sext (extract v_8079 8 16) 10) (sext (extract v_8082 8 16) 10));
      v_8105 <- eval (sub (sext (extract v_8079 16 24) 10) (sext (extract v_8082 16 24) 10));
      v_8115 <- eval (sub (sext (extract v_8079 24 32) 10) (sext (extract v_8082 24 32) 10));
      v_8125 <- eval (sub (sext (extract v_8079 32 40) 10) (sext (extract v_8082 32 40) 10));
      v_8135 <- eval (sub (sext (extract v_8079 40 48) 10) (sext (extract v_8082 40 48) 10));
      v_8145 <- eval (sub (sext (extract v_8079 48 56) 10) (sext (extract v_8082 48 56) 10));
      v_8155 <- eval (sub (sext (extract v_8079 56 64) 10) (sext (extract v_8082 56 64) 10));
      v_8165 <- eval (sub (sext (extract v_8079 64 72) 10) (sext (extract v_8082 64 72) 10));
      v_8175 <- eval (sub (sext (extract v_8079 72 80) 10) (sext (extract v_8082 72 80) 10));
      v_8185 <- eval (sub (sext (extract v_8079 80 88) 10) (sext (extract v_8082 80 88) 10));
      v_8195 <- eval (sub (sext (extract v_8079 88 96) 10) (sext (extract v_8082 88 96) 10));
      v_8205 <- eval (sub (sext (extract v_8079 96 104) 10) (sext (extract v_8082 96 104) 10));
      v_8215 <- eval (sub (sext (extract v_8079 104 112) 10) (sext (extract v_8082 104 112) 10));
      v_8225 <- eval (sub (sext (extract v_8079 112 120) 10) (sext (extract v_8082 112 120) 10));
      v_8235 <- eval (sub (sext (extract v_8079 120 128) 10) (sext (extract v_8082 120 128) 10));
      setRegister (lhs.of_reg v_3200) (concat (mux (sgt v_8085 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_8085 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_8085 2 10))) (concat (mux (sgt v_8095 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_8095 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_8095 2 10))) (concat (mux (sgt v_8105 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_8105 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_8105 2 10))) (concat (mux (sgt v_8115 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_8115 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_8115 2 10))) (concat (mux (sgt v_8125 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_8125 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_8125 2 10))) (concat (mux (sgt v_8135 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_8135 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_8135 2 10))) (concat (mux (sgt v_8145 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_8145 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_8145 2 10))) (concat (mux (sgt v_8155 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_8155 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_8155 2 10))) (concat (mux (sgt v_8165 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_8165 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_8165 2 10))) (concat (mux (sgt v_8175 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_8175 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_8175 2 10))) (concat (mux (sgt v_8185 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_8185 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_8185 2 10))) (concat (mux (sgt v_8195 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_8195 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_8195 2 10))) (concat (mux (sgt v_8205 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_8205 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_8205 2 10))) (concat (mux (sgt v_8215 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_8215 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_8215 2 10))) (concat (mux (sgt v_8225 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_8225 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_8225 2 10))) (mux (sgt v_8235 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_8235 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_8235 2 10))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3195 : Mem) (v_3196 : reg (bv 128)) => do
      v_14500 <- getRegister v_3196;
      v_14503 <- evaluateAddress v_3195;
      v_14504 <- load v_14503 16;
      v_14507 <- eval (sub (sext (extract v_14500 0 8) 10) (sext (extract v_14504 0 8) 10));
      v_14517 <- eval (sub (sext (extract v_14500 8 16) 10) (sext (extract v_14504 8 16) 10));
      v_14527 <- eval (sub (sext (extract v_14500 16 24) 10) (sext (extract v_14504 16 24) 10));
      v_14537 <- eval (sub (sext (extract v_14500 24 32) 10) (sext (extract v_14504 24 32) 10));
      v_14547 <- eval (sub (sext (extract v_14500 32 40) 10) (sext (extract v_14504 32 40) 10));
      v_14557 <- eval (sub (sext (extract v_14500 40 48) 10) (sext (extract v_14504 40 48) 10));
      v_14567 <- eval (sub (sext (extract v_14500 48 56) 10) (sext (extract v_14504 48 56) 10));
      v_14577 <- eval (sub (sext (extract v_14500 56 64) 10) (sext (extract v_14504 56 64) 10));
      v_14587 <- eval (sub (sext (extract v_14500 64 72) 10) (sext (extract v_14504 64 72) 10));
      v_14597 <- eval (sub (sext (extract v_14500 72 80) 10) (sext (extract v_14504 72 80) 10));
      v_14607 <- eval (sub (sext (extract v_14500 80 88) 10) (sext (extract v_14504 80 88) 10));
      v_14617 <- eval (sub (sext (extract v_14500 88 96) 10) (sext (extract v_14504 88 96) 10));
      v_14627 <- eval (sub (sext (extract v_14500 96 104) 10) (sext (extract v_14504 96 104) 10));
      v_14637 <- eval (sub (sext (extract v_14500 104 112) 10) (sext (extract v_14504 104 112) 10));
      v_14647 <- eval (sub (sext (extract v_14500 112 120) 10) (sext (extract v_14504 112 120) 10));
      v_14657 <- eval (sub (sext (extract v_14500 120 128) 10) (sext (extract v_14504 120 128) 10));
      setRegister (lhs.of_reg v_3196) (concat (mux (sgt v_14507 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_14507 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_14507 2 10))) (concat (mux (sgt v_14517 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_14517 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_14517 2 10))) (concat (mux (sgt v_14527 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_14527 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_14527 2 10))) (concat (mux (sgt v_14537 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_14537 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_14537 2 10))) (concat (mux (sgt v_14547 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_14547 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_14547 2 10))) (concat (mux (sgt v_14557 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_14557 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_14557 2 10))) (concat (mux (sgt v_14567 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_14567 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_14567 2 10))) (concat (mux (sgt v_14577 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_14577 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_14577 2 10))) (concat (mux (sgt v_14587 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_14587 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_14587 2 10))) (concat (mux (sgt v_14597 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_14597 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_14597 2 10))) (concat (mux (sgt v_14607 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_14607 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_14607 2 10))) (concat (mux (sgt v_14617 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_14617 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_14617 2 10))) (concat (mux (sgt v_14627 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_14627 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_14627 2 10))) (concat (mux (sgt v_14637 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_14637 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_14637 2 10))) (concat (mux (sgt v_14647 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_14647 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_14647 2 10))) (mux (sgt v_14657 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_14657 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_14657 2 10))))))))))))))))));
      pure ()
    pat_end

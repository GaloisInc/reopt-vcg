def vpsravd1 : instruction :=
  definst "vpsravd" $ do
    pattern fun (v_3231 : reg (bv 128)) (v_3232 : reg (bv 128)) (v_3233 : reg (bv 128)) => do
      v_8790 <- getRegister v_3232;
      v_8791 <- eval (extract v_8790 0 32);
      v_8795 <- getRegister v_3231;
      v_8799 <- eval (extract v_8790 32 64);
      v_8806 <- eval (extract v_8790 64 96);
      v_8813 <- eval (extract v_8790 96 128);
      setRegister (lhs.of_reg v_3233) (concat (ashr (mi (bitwidthMInt v_8791) (svalueMInt v_8791)) (uvalueMInt (extract v_8795 0 32))) (concat (ashr (mi (bitwidthMInt v_8799) (svalueMInt v_8799)) (uvalueMInt (extract v_8795 32 64))) (concat (ashr (mi (bitwidthMInt v_8806) (svalueMInt v_8806)) (uvalueMInt (extract v_8795 64 96))) (ashr (mi (bitwidthMInt v_8813) (svalueMInt v_8813)) (uvalueMInt (extract v_8795 96 128))))));
      pure ()
    pat_end;
    pattern fun (v_3242 : reg (bv 256)) (v_3243 : reg (bv 256)) (v_3244 : reg (bv 256)) => do
      v_8829 <- getRegister v_3243;
      v_8830 <- eval (extract v_8829 0 32);
      v_8834 <- getRegister v_3242;
      v_8838 <- eval (extract v_8829 32 64);
      v_8845 <- eval (extract v_8829 64 96);
      v_8852 <- eval (extract v_8829 96 128);
      v_8859 <- eval (extract v_8829 128 160);
      v_8866 <- eval (extract v_8829 160 192);
      v_8873 <- eval (extract v_8829 192 224);
      v_8880 <- eval (extract v_8829 224 256);
      setRegister (lhs.of_reg v_3244) (concat (ashr (mi (bitwidthMInt v_8830) (svalueMInt v_8830)) (uvalueMInt (extract v_8834 0 32))) (concat (ashr (mi (bitwidthMInt v_8838) (svalueMInt v_8838)) (uvalueMInt (extract v_8834 32 64))) (concat (ashr (mi (bitwidthMInt v_8845) (svalueMInt v_8845)) (uvalueMInt (extract v_8834 64 96))) (concat (ashr (mi (bitwidthMInt v_8852) (svalueMInt v_8852)) (uvalueMInt (extract v_8834 96 128))) (concat (ashr (mi (bitwidthMInt v_8859) (svalueMInt v_8859)) (uvalueMInt (extract v_8834 128 160))) (concat (ashr (mi (bitwidthMInt v_8866) (svalueMInt v_8866)) (uvalueMInt (extract v_8834 160 192))) (concat (ashr (mi (bitwidthMInt v_8873) (svalueMInt v_8873)) (uvalueMInt (extract v_8834 192 224))) (ashr (mi (bitwidthMInt v_8880) (svalueMInt v_8880)) (uvalueMInt (extract v_8834 224 256))))))))));
      pure ()
    pat_end;
    pattern fun (v_3228 : Mem) (v_3226 : reg (bv 128)) (v_3227 : reg (bv 128)) => do
      v_15395 <- getRegister v_3226;
      v_15396 <- eval (extract v_15395 0 32);
      v_15400 <- evaluateAddress v_3228;
      v_15401 <- load v_15400 16;
      v_15405 <- eval (extract v_15395 32 64);
      v_15412 <- eval (extract v_15395 64 96);
      v_15419 <- eval (extract v_15395 96 128);
      setRegister (lhs.of_reg v_3227) (concat (ashr (mi (bitwidthMInt v_15396) (svalueMInt v_15396)) (uvalueMInt (extract v_15401 0 32))) (concat (ashr (mi (bitwidthMInt v_15405) (svalueMInt v_15405)) (uvalueMInt (extract v_15401 32 64))) (concat (ashr (mi (bitwidthMInt v_15412) (svalueMInt v_15412)) (uvalueMInt (extract v_15401 64 96))) (ashr (mi (bitwidthMInt v_15419) (svalueMInt v_15419)) (uvalueMInt (extract v_15401 96 128))))));
      pure ()
    pat_end;
    pattern fun (v_3237 : Mem) (v_3238 : reg (bv 256)) (v_3239 : reg (bv 256)) => do
      v_15430 <- getRegister v_3238;
      v_15431 <- eval (extract v_15430 0 32);
      v_15435 <- evaluateAddress v_3237;
      v_15436 <- load v_15435 32;
      v_15440 <- eval (extract v_15430 32 64);
      v_15447 <- eval (extract v_15430 64 96);
      v_15454 <- eval (extract v_15430 96 128);
      v_15461 <- eval (extract v_15430 128 160);
      v_15468 <- eval (extract v_15430 160 192);
      v_15475 <- eval (extract v_15430 192 224);
      v_15482 <- eval (extract v_15430 224 256);
      setRegister (lhs.of_reg v_3239) (concat (ashr (mi (bitwidthMInt v_15431) (svalueMInt v_15431)) (uvalueMInt (extract v_15436 0 32))) (concat (ashr (mi (bitwidthMInt v_15440) (svalueMInt v_15440)) (uvalueMInt (extract v_15436 32 64))) (concat (ashr (mi (bitwidthMInt v_15447) (svalueMInt v_15447)) (uvalueMInt (extract v_15436 64 96))) (concat (ashr (mi (bitwidthMInt v_15454) (svalueMInt v_15454)) (uvalueMInt (extract v_15436 96 128))) (concat (ashr (mi (bitwidthMInt v_15461) (svalueMInt v_15461)) (uvalueMInt (extract v_15436 128 160))) (concat (ashr (mi (bitwidthMInt v_15468) (svalueMInt v_15468)) (uvalueMInt (extract v_15436 160 192))) (concat (ashr (mi (bitwidthMInt v_15475) (svalueMInt v_15475)) (uvalueMInt (extract v_15436 192 224))) (ashr (mi (bitwidthMInt v_15482) (svalueMInt v_15482)) (uvalueMInt (extract v_15436 224 256))))))))));
      pure ()
    pat_end

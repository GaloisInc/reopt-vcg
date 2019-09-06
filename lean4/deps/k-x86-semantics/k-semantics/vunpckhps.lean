def vunpckhps1 : instruction :=
  definst "vunpckhps" $ do
    pattern fun (v_3249 : reg (bv 128)) (v_3250 : reg (bv 128)) (v_3251 : reg (bv 128)) => do
      v_7569 <- getRegister v_3249;
      v_7571 <- getRegister v_3250;
      setRegister (lhs.of_reg v_3251) (concat (concat (concat (extract v_7569 0 32) (extract v_7571 0 32)) (extract v_7569 32 64)) (extract v_7571 32 64));
      pure ()
    pat_end;
    pattern fun (v_3260 : reg (bv 256)) (v_3261 : reg (bv 256)) (v_3262 : reg (bv 256)) => do
      v_7584 <- getRegister v_3260;
      v_7586 <- getRegister v_3261;
      setRegister (lhs.of_reg v_3262) (concat (concat (concat (concat (extract v_7584 0 32) (extract v_7586 0 32)) (extract v_7584 32 64)) (extract v_7586 32 64)) (concat (concat (concat (extract v_7584 128 160) (extract v_7586 128 160)) (extract v_7584 160 192)) (extract v_7586 160 192)));
      pure ()
    pat_end;
    pattern fun (v_3243 : Mem) (v_3244 : reg (bv 128)) (v_3245 : reg (bv 128)) => do
      v_13441 <- evaluateAddress v_3243;
      v_13442 <- load v_13441 16;
      v_13444 <- getRegister v_3244;
      setRegister (lhs.of_reg v_3245) (concat (concat (concat (extract v_13442 0 32) (extract v_13444 0 32)) (extract v_13442 32 64)) (extract v_13444 32 64));
      pure ()
    pat_end;
    pattern fun (v_3254 : Mem) (v_3255 : reg (bv 256)) (v_3256 : reg (bv 256)) => do
      v_13452 <- evaluateAddress v_3254;
      v_13453 <- load v_13452 32;
      v_13455 <- getRegister v_3255;
      setRegister (lhs.of_reg v_3256) (concat (concat (concat (concat (extract v_13453 0 32) (extract v_13455 0 32)) (extract v_13453 32 64)) (extract v_13455 32 64)) (concat (concat (concat (extract v_13453 128 160) (extract v_13455 128 160)) (extract v_13453 160 192)) (extract v_13455 160 192)));
      pure ()
    pat_end

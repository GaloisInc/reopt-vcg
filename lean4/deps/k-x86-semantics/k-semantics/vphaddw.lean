def vphaddw1 : instruction :=
  definst "vphaddw" $ do
    pattern fun (v_3258 : reg (bv 128)) (v_3259 : reg (bv 128)) (v_3260 : reg (bv 128)) => do
      v_9003 <- getRegister v_3258;
      v_9019 <- getRegister v_3259;
      setRegister (lhs.of_reg v_3260) (concat (concat (concat (concat (concat (concat (concat (add (extract v_9003 0 16) (extract v_9003 16 32)) (add (extract v_9003 32 48) (extract v_9003 48 64))) (add (extract v_9003 64 80) (extract v_9003 80 96))) (add (extract v_9003 96 112) (extract v_9003 112 128))) (add (extract v_9019 0 16) (extract v_9019 16 32))) (add (extract v_9019 32 48) (extract v_9019 48 64))) (add (extract v_9019 64 80) (extract v_9019 80 96))) (add (extract v_9019 96 112) (extract v_9019 112 128)));
      pure ()
    pat_end;
    pattern fun (v_3268 : reg (bv 256)) (v_3269 : reg (bv 256)) (v_3270 : reg (bv 256)) => do
      v_9042 <- getRegister v_3268;
      v_9058 <- getRegister v_3269;
      setRegister (lhs.of_reg v_3270) (concat (concat (concat (concat (concat (concat (concat (concat (add (extract v_9042 0 16) (extract v_9042 16 32)) (add (extract v_9042 32 48) (extract v_9042 48 64))) (add (extract v_9042 64 80) (extract v_9042 80 96))) (add (extract v_9042 96 112) (extract v_9042 112 128))) (add (extract v_9058 0 16) (extract v_9058 16 32))) (add (extract v_9058 32 48) (extract v_9058 48 64))) (add (extract v_9058 64 80) (extract v_9058 80 96))) (add (extract v_9058 96 112) (extract v_9058 112 128))) (concat (concat (concat (concat (concat (concat (concat (add (extract v_9042 128 144) (extract v_9042 144 160)) (add (extract v_9042 160 176) (extract v_9042 176 192))) (add (extract v_9042 192 208) (extract v_9042 208 224))) (add (extract v_9042 224 240) (extract v_9042 240 256))) (add (extract v_9058 128 144) (extract v_9058 144 160))) (add (extract v_9058 160 176) (extract v_9058 176 192))) (add (extract v_9058 192 208) (extract v_9058 208 224))) (add (extract v_9058 224 240) (extract v_9058 240 256))));
      pure ()
    pat_end;
    pattern fun (v_3252 : Mem) (v_3253 : reg (bv 128)) (v_3254 : reg (bv 128)) => do
      v_17407 <- evaluateAddress v_3252;
      v_17408 <- load v_17407 16;
      v_17424 <- getRegister v_3253;
      setRegister (lhs.of_reg v_3254) (concat (concat (concat (concat (concat (concat (concat (add (extract v_17408 0 16) (extract v_17408 16 32)) (add (extract v_17408 32 48) (extract v_17408 48 64))) (add (extract v_17408 64 80) (extract v_17408 80 96))) (add (extract v_17408 96 112) (extract v_17408 112 128))) (add (extract v_17424 0 16) (extract v_17424 16 32))) (add (extract v_17424 32 48) (extract v_17424 48 64))) (add (extract v_17424 64 80) (extract v_17424 80 96))) (add (extract v_17424 96 112) (extract v_17424 112 128)));
      pure ()
    pat_end;
    pattern fun (v_3263 : Mem) (v_3264 : reg (bv 256)) (v_3265 : reg (bv 256)) => do
      v_17442 <- evaluateAddress v_3263;
      v_17443 <- load v_17442 32;
      v_17459 <- getRegister v_3264;
      setRegister (lhs.of_reg v_3265) (concat (concat (concat (concat (concat (concat (concat (concat (add (extract v_17443 0 16) (extract v_17443 16 32)) (add (extract v_17443 32 48) (extract v_17443 48 64))) (add (extract v_17443 64 80) (extract v_17443 80 96))) (add (extract v_17443 96 112) (extract v_17443 112 128))) (add (extract v_17459 0 16) (extract v_17459 16 32))) (add (extract v_17459 32 48) (extract v_17459 48 64))) (add (extract v_17459 64 80) (extract v_17459 80 96))) (add (extract v_17459 96 112) (extract v_17459 112 128))) (concat (concat (concat (concat (concat (concat (concat (add (extract v_17443 128 144) (extract v_17443 144 160)) (add (extract v_17443 160 176) (extract v_17443 176 192))) (add (extract v_17443 192 208) (extract v_17443 208 224))) (add (extract v_17443 224 240) (extract v_17443 240 256))) (add (extract v_17459 128 144) (extract v_17459 144 160))) (add (extract v_17459 160 176) (extract v_17459 176 192))) (add (extract v_17459 192 208) (extract v_17459 208 224))) (add (extract v_17459 224 240) (extract v_17459 240 256))));
      pure ()
    pat_end

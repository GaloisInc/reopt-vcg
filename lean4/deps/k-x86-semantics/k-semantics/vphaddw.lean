def vphaddw1 : instruction :=
  definst "vphaddw" $ do
    pattern fun (v_3204 : reg (bv 128)) (v_3205 : reg (bv 128)) (v_3206 : reg (bv 128)) => do
      v_9148 <- getRegister v_3204;
      v_9164 <- getRegister v_3205;
      setRegister (lhs.of_reg v_3206) (concat (concat (concat (concat (concat (concat (concat (add (extract v_9148 0 16) (extract v_9148 16 32)) (add (extract v_9148 32 48) (extract v_9148 48 64))) (add (extract v_9148 64 80) (extract v_9148 80 96))) (add (extract v_9148 96 112) (extract v_9148 112 128))) (add (extract v_9164 0 16) (extract v_9164 16 32))) (add (extract v_9164 32 48) (extract v_9164 48 64))) (add (extract v_9164 64 80) (extract v_9164 80 96))) (add (extract v_9164 96 112) (extract v_9164 112 128)));
      pure ()
    pat_end;
    pattern fun (v_3218 : reg (bv 256)) (v_3219 : reg (bv 256)) (v_3220 : reg (bv 256)) => do
      v_9187 <- getRegister v_3218;
      v_9203 <- getRegister v_3219;
      setRegister (lhs.of_reg v_3220) (concat (concat (concat (concat (concat (concat (concat (concat (add (extract v_9187 0 16) (extract v_9187 16 32)) (add (extract v_9187 32 48) (extract v_9187 48 64))) (add (extract v_9187 64 80) (extract v_9187 80 96))) (add (extract v_9187 96 112) (extract v_9187 112 128))) (add (extract v_9203 0 16) (extract v_9203 16 32))) (add (extract v_9203 32 48) (extract v_9203 48 64))) (add (extract v_9203 64 80) (extract v_9203 80 96))) (add (extract v_9203 96 112) (extract v_9203 112 128))) (concat (concat (concat (concat (concat (concat (concat (add (extract v_9187 128 144) (extract v_9187 144 160)) (add (extract v_9187 160 176) (extract v_9187 176 192))) (add (extract v_9187 192 208) (extract v_9187 208 224))) (add (extract v_9187 224 240) (extract v_9187 240 256))) (add (extract v_9203 128 144) (extract v_9203 144 160))) (add (extract v_9203 160 176) (extract v_9203 176 192))) (add (extract v_9203 192 208) (extract v_9203 208 224))) (add (extract v_9203 224 240) (extract v_9203 240 256))));
      pure ()
    pat_end;
    pattern fun (v_3203 : Mem) (v_3199 : reg (bv 128)) (v_3200 : reg (bv 128)) => do
      v_17794 <- evaluateAddress v_3203;
      v_17795 <- load v_17794 16;
      v_17811 <- getRegister v_3199;
      setRegister (lhs.of_reg v_3200) (concat (concat (concat (concat (concat (concat (concat (add (extract v_17795 0 16) (extract v_17795 16 32)) (add (extract v_17795 32 48) (extract v_17795 48 64))) (add (extract v_17795 64 80) (extract v_17795 80 96))) (add (extract v_17795 96 112) (extract v_17795 112 128))) (add (extract v_17811 0 16) (extract v_17811 16 32))) (add (extract v_17811 32 48) (extract v_17811 48 64))) (add (extract v_17811 64 80) (extract v_17811 80 96))) (add (extract v_17811 96 112) (extract v_17811 112 128)));
      pure ()
    pat_end;
    pattern fun (v_3212 : Mem) (v_3213 : reg (bv 256)) (v_3214 : reg (bv 256)) => do
      v_17829 <- evaluateAddress v_3212;
      v_17830 <- load v_17829 32;
      v_17846 <- getRegister v_3213;
      setRegister (lhs.of_reg v_3214) (concat (concat (concat (concat (concat (concat (concat (concat (add (extract v_17830 0 16) (extract v_17830 16 32)) (add (extract v_17830 32 48) (extract v_17830 48 64))) (add (extract v_17830 64 80) (extract v_17830 80 96))) (add (extract v_17830 96 112) (extract v_17830 112 128))) (add (extract v_17846 0 16) (extract v_17846 16 32))) (add (extract v_17846 32 48) (extract v_17846 48 64))) (add (extract v_17846 64 80) (extract v_17846 80 96))) (add (extract v_17846 96 112) (extract v_17846 112 128))) (concat (concat (concat (concat (concat (concat (concat (add (extract v_17830 128 144) (extract v_17830 144 160)) (add (extract v_17830 160 176) (extract v_17830 176 192))) (add (extract v_17830 192 208) (extract v_17830 208 224))) (add (extract v_17830 224 240) (extract v_17830 240 256))) (add (extract v_17846 128 144) (extract v_17846 144 160))) (add (extract v_17846 160 176) (extract v_17846 176 192))) (add (extract v_17846 192 208) (extract v_17846 208 224))) (add (extract v_17846 224 240) (extract v_17846 240 256))));
      pure ()
    pat_end
